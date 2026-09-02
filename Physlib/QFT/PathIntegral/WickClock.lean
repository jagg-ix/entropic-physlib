/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QFT.PathIntegral.FeynmanKac
public import Physlib.QFT.PathIntegral.Lorentzian
public import Physlib.QFT.Matsubara.PathIntegral
public import Physlib.QFT.PathIntegral.DampedHeatLandauerDichotomy
public import Physlib.Units.WithDim.Mass
meta import Zil

/-!
# Wick clock: scalar Lorentzian ↔ Euclidean time-coordinate conversion

A coordinate-level scalar layer that ties the existing kernel-level Wick
rotation (`Physlib.QuantumMechanics.NonHermitian.WickRotation`) to the
**Lorentzian (real-time) ↔ Euclidean (imaginary-time)** correspondence
at the path-integral and entropic-time layer.

The defining substitution is

  `t  =  −i · τ_E`,

where `t ∈ ℝ` is real Lorentzian time and `τ_E ∈ ℝ` is Euclidean
imaginary time.  Under this substitution:

* **Metric-signature flip** — the squared Lorentzian time-element `t²`
  becomes `−τ_E²`, so a purely-timelike Lorentzian proper time
  `τ_L = −i·τ_E` satisfies `τ_L² = −τ_E²` (`wickRotate_sq`,
  `properTime_lorentz_to_euclidean_sq`).
* **Reversible-sector reduction** — the Lorentzian unitary phase
  `exp(−i·E_R·t/ℏ)` becomes the real Euclidean heat kernel
  `exp(−E_R·τ_E/ℏ)` (`reversiblePhase_at_wickRotate`).
* **Reversible Lorentzian propagator at `H_I = 0`** reduces to the
  real Euclidean exponential (`lorentzianPropagator_at_wickRotate_HI_zero`).
* **Thermal Boltzmann reduction** — at the thermal period `τ_E = βℏ`,
  the Wick-rotated reversible phase is the Boltzmann weight
  `exp(−βE_R)` (`reversiblePhase_at_wickRotate_thermalPeriod`).
* **Damping invariance** — the path-integral damping
  `exp(−S_I/ℏ)` is real, lives in the modulus, and is *unchanged* by
  the Wick rotation of the reversible-sector phase
  (`path_integral_damping_is_real`,
  `lorentzianKernel_modulus_invariant_under_wick`).

The result is a focused, scalar coordinate-level interface to the
existing kernel-level Wick rotation, made composable with the
just-shipped `RindlerEntropicTime` and `LorentzInvariant` modules.

The full **typed-tensor metric rotation** (rotating the Minkowski metric
to Euclidean signature on physlib's `Lorentz` tensor stack) is a
separate, larger development and is not attempted here.


## References

- **Mazur & Ulam 1932** — *Sur les transformations isométriques d'espaces vectoriels normés*
- **Wick 1954** — *Properties of Bethe-Salpeter Wave Functions*
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QFT.PathIntegral

open Complex Physlib.QuantumMechanics.NonHermitian.WickRotation
  Physlib.QFT.Matsubara.PathIntegral


/-- **Wick rotation substitution**: takes a real Euclidean time `τ_E`
to the complex Lorentzian time `t = −i · τ_E`. -/
def wickRotate (τ_E : ℝ) : ℂ := -Complex.I * (τ_E : ℂ)

/-- **Inverse Wick rotation**: takes a real Lorentzian time `t` to the
complex Euclidean time `i · t`. -/
def wickRotateInv (t : ℝ) : ℂ := Complex.I * (t : ℂ)

@[simp] lemma wickRotate_zero : wickRotate 0 = 0 := by
  unfold wickRotate; simp

@[simp] lemma wickRotateInv_zero : wickRotateInv 0 = 0 := by
  unfold wickRotateInv; simp

/-- Wick rotation is odd: `wickRotate (−τ_E) = − wickRotate τ_E`. -/
lemma wickRotate_neg (τ_E : ℝ) :
    wickRotate (-τ_E) = -wickRotate τ_E := by
  unfold wickRotate; push_cast; ring

/-- Real part of the Wick-rotated time is zero (purely imaginary). -/
@[simp] lemma wickRotate_re (τ_E : ℝ) : (wickRotate τ_E).re = 0 := by
  unfold wickRotate; simp

/-- Imaginary part of the Wick-rotated time is `−τ_E`. -/
@[simp] lemma wickRotate_im (τ_E : ℝ) : (wickRotate τ_E).im = -τ_E := by
  unfold wickRotate; simp


/-- **Metric-signature flip.** Under Wick rotation the squared Lorentzian
time-element `t²` becomes minus the squared Euclidean time-element `τ_E²`:
`(wickRotate τ_E)² = −(τ_E : ℂ)²`.

This is the *coordinate-level* expression of the Lorentzian → Euclidean
signature change `dt² ↦ −dτ_E²` (equivalently, in `(+−−−)` Minkowski
signature, the timelike component contributes `−` to the Lorentzian
line element and `+` to the Euclidean line element). -/
lemma wickRotate_sq (τ_E : ℝ) :
    (wickRotate τ_E) ^ 2 = -((τ_E : ℂ) ^ 2) := by
  unfold wickRotate
  have hI2 : (-Complex.I) ^ 2 = -1 := by
    rw [neg_pow, Complex.I_sq]
    simp
  calc (-Complex.I * (τ_E : ℂ)) ^ 2
      = (-Complex.I) ^ 2 * (τ_E : ℂ) ^ 2 := by ring
    _ = (-1) * (τ_E : ℂ) ^ 2 := by rw [hI2]
    _ = -((τ_E : ℂ) ^ 2) := by ring

/-- **Purely-timelike Lorentzian proper time as imaginary Euclidean time.**
For a purely timelike segment (`dx = 0`), the Lorentzian proper-time
element `dτ_L = dt` and its Wick-rotated counterpart `τ_L = −i·τ_E`
satisfy `τ_L² = −τ_E²`. -/
lemma properTime_lorentz_to_euclidean_sq (τ_E : ℝ) :
    (wickRotate τ_E) ^ 2 = -((τ_E : ℂ) ^ 2) :=
  wickRotate_sq τ_E


/-- **Reversible-sector Wick reduction.**  The complex-time reversible
phase `reversiblePhaseC E_R ℏ t = exp(−i·E_R·t/ℏ)`, evaluated at the
Wick-rotated time `t = wickRotate τ_E`, becomes the real Euclidean
heat kernel `exp(−E_R·τ_E/ℏ)`.  This is the
`reversiblePhase_wickRotation` theorem stated via the named operator. -/
lemma reversiblePhase_at_wickRotate (E_R ℏ τ_E : ℝ) :
    reversiblePhaseC E_R ℏ (wickRotate τ_E) =
      ((Real.exp (-(E_R * τ_E / ℏ)) : ℝ) : ℂ) := by
  unfold wickRotate
  exact reversiblePhase_wickRotation E_R ℏ τ_E

/-- **Lorentzian propagator at `H_I = 0` reduces to the Euclidean heat
kernel under Wick rotation.**  For a purely-Hermitian Hamiltonian
(`H_I = 0`), the Lorentzian scalar propagator viewed via
`reversiblePhaseC`, at the Wick-rotated time, becomes the real
Euclidean exponential. -/
lemma lorentzianPropagator_at_wickRotate_HI_zero
    (H_R ℏ τ_E : ℝ) :
    reversiblePhaseC H_R ℏ (wickRotate τ_E) =
      ((Real.exp (-(H_R * τ_E / ℏ)) : ℝ) : ℂ) :=
  reversiblePhase_at_wickRotate H_R ℏ τ_E


/-- **Wick at the thermal period gives the Boltzmann weight.**  At
`τ_E = βℏ` (one full period of the thermal circle), the Wick-rotated
reversible phase is the Boltzmann weight `exp(−βE_R)`. -/
lemma reversiblePhase_at_wickRotate_thermalPeriod
    (E_R : ℝ) (T : ThermalCircle) :
    reversiblePhaseC E_R T.hbar (wickRotate T.period) =
      ((Real.exp (-(T.beta * E_R)) : ℝ) : ℂ) := by
  unfold wickRotate
  exact euclidean_reversiblePhase_at_thermalPeriod_eq_boltzmann E_R T

/-- The Boltzmann weight `exp(−βE_R)` is the one-period Wick rotation,
restated through the `wickRotate` operator. -/
lemma matsubaraWeight_eq_wickRotate (E_R : ℝ) (T : ThermalCircle) :
    matsubaraWeight E_R T = reversiblePhaseC E_R T.hbar (wickRotate T.period) :=
  (reversiblePhase_at_wickRotate_thermalPeriod E_R T).symm


/-- **`path_integral_damping` is a real coercion.**  The scalar
path-integral damping factor is a *real* number `exp(−S_I/ℏ)`; viewed
as `ℂ`, it is `Complex.ofReal` of a real exponential — entirely in the
modulus, not the phase. -/
lemma path_integral_damping_eq_real (ℏ S_I : ℝ) :
    ((path_integral_damping ℏ S_I : ℝ) : ℂ) =
      ((Real.exp (- S_I / ℏ) : ℝ) : ℂ) := by
  unfold path_integral_damping
  rfl

/-- **Modulus invariance under Wick.**  The Wick rotation rotates the
reversible-sector *phase*, but the entropic damping
`‖lorentzianKernel S_R S_I ℏ‖ = exp(−S_I/ℏ)` is a modulus-level scalar:
it does not depend on the time direction.  Stated as the modulus of the
existing Lorentzian kernel, which equals `path_integral_damping` and is
*Wick-rotation invariant by construction* (independent of any time
parameter). -/
lemma lorentzianKernel_modulus_invariant_under_wick
    (S_R S_I ℏ : ℝ) :
    ‖lorentzianKernel S_R S_I ℏ‖ = path_integral_damping ℏ S_I := by
  rw [lorentzianKernel_norm_eq_path_integral_damping]


/-- **NS Stokes diffusion kernel from Wick rotation of the reversible
phase.**

Per Fourier mode `k`, the incompressible NS Stokes diffusion semigroup
`exp(−ν · k² · τ_E)` (kinematic viscosity `ν > 0`) is the Wick-rotated
reversible phase `reversiblePhaseC E_k ℏ (wickRotate τ_E)` of an
associated quantum system with **mode energy** `E_k := ℏ · ν · k²`.

Substituting `E_R = E_k = ℏ · ν · k²` into
`reversiblePhase_at_wickRotate`:

  `exp(−i · E_k · t / ℏ)` at `t = wickRotate τ_E`
   ⟶  `exp(−E_k · τ_E / ℏ) = exp(−ν · k² · τ_E)`

— the NS Stokes diffusion kernel is **identical** to the Wick-rotated
unitary phase of an `E_k = ℏν k²` mode.  This bridges NS (parabolic /
dissipative) to the reversible-sector phase of the entropic-time QM (hyperbolic /
unitary) through the Wick clock. -/
lemma ns_stokesKernel_eq_wickRotated_reversiblePhase
    (ν k_sq τ_E ℏ : ℝ) (hℏ : ℏ ≠ 0) :
    reversiblePhaseC (ℏ * ν * k_sq) ℏ (wickRotate τ_E) =
      ((Real.exp (-(ν * k_sq * τ_E)) : ℝ) : ℂ) := by
  rw [reversiblePhase_at_wickRotate]
  congr 2
  rw [show ℏ * ν * k_sq * τ_E / ℏ = ν * k_sq * τ_E from by field_simp]

/-!

The kernel-level identity above is upgraded to a full **ODE-level** derivation
of the NS Stokes equation from the Schrödinger equation under Wick rotation.

**Chain of reasoning**:

1. *Schrödinger ODE (eigen-form).* The complex unitary phase
   `u(t) = exp(−i · E · t / ℏ)` satisfies `iℏ · u̇(t) = E · u(t)`
   (`Physlib.QuantumMechanics.NonHermitian.WickRotation.nonHermitian_schrodinger_eigen`,
   already shipped — a genuine `HasDerivAt`, not a definitional restatement).

2. *Wick substitution `t = −i · τ_E`* turns the complex phase into a real
   exponential `u(−i · τ_E) = exp(−E · τ_E / ℏ)`
   (`reversiblePhase_at_wickRotate`).

3. *The Wick-rotated function satisfies the heat-equation ODE in `τ_E`*
   (`wickRotated_schrodinger_satisfies_heatEq`):
   `d/dτ_E [exp(−(E/ℏ) · τ_E)] = −(E/ℏ) · exp(−(E/ℏ) · τ_E)`.

4. *NS Stokes ODE per Fourier mode* (`ns_stokes_mode_satisfies_ODE`):
   for `u_k(t) := exp(−(ν · k²) · t)`,
   `d/dt u_k(t) = −(ν · k²) · u_k(t)`.

5. *Identification.*  At `E_k = ℏ · ν · k²` the rate constants match:
   `E_k / ℏ = ν · k²`.  The Wick-rotated Schrödinger ODE in `τ_E` for the
   `E_k`-mode is **literally** the NS Stokes ODE in `t` for Fourier mode `k`
   (`ns_stokes_eq_wickRotated_schrodinger_funext`).

The two ODEs are the *same* first-order linear decay equation under the
Madelung / Nelson stochastic-mechanics identification `E_k = ℏ · ν · k²`.
-/

/-- **(Step 3) Wick-rotated Schrödinger phase satisfies the heat-equation
ODE in `τ_E`.**  The real exponential `exp(−(E/ℏ) · τ_E)` — the Wick-rotated
form of the Schrödinger phase — satisfies the first-order linear decay ODE
`dψ/dτ_E = −(E/ℏ) · ψ`.  This is the dynamical content of the Wick rotation:
the complex Schrödinger ODE `iℏ ψ̇ = E · ψ` reduces under `t = −i · τ_E` to
the real heat-equation ODE `ψ̇ = −(E/ℏ) · ψ`. -/
lemma wickRotated_schrodinger_satisfies_heatEq (E ℏ : ℝ) :
    ∀ τ_E : ℝ, HasDerivAt (fun s : ℝ => Real.exp (-(E / ℏ) * s))
      (-(E / ℏ) * Real.exp (-(E / ℏ) * τ_E)) τ_E :=
  damping_satisfies_decay_ODE (E / ℏ)

/-- **(Step 4) NS Stokes ODE per Fourier mode `k`.**  The Stokes diffusion
solution `u_k(t) = exp(−ν · k² · t)` satisfies
`du_k/dt = −(ν · k²) · u_k(t)`.  Direct specialisation of
`damping_satisfies_decay_ODE` with `V = ν · k²`. -/
lemma ns_stokes_mode_satisfies_ODE (ν k_sq : ℝ) :
    ∀ t : ℝ, HasDerivAt (fun s : ℝ => Real.exp (-(ν * k_sq) * s))
      (-(ν * k_sq) * Real.exp (-(ν * k_sq) * t)) t :=
  damping_satisfies_decay_ODE (ν * k_sq)

/-- **(Step 5) Madelung / Nelson identification: `E_k = ℏ · ν · k²` makes
the Wick-rotated Schrödinger and the NS Stokes ODE-solutions identical
functions.**

Both ODEs have the form `df/ds = −V · f(s)` with explicit solution
`exp(−V · s)`.  Setting `V = E_k / ℏ` (Wick-rotated Schrödinger) and
`V = ν · k²` (NS Stokes), the rate constants coincide exactly when
`E_k = ℏ · ν · k²`. -/
lemma ns_stokes_eq_wickRotated_schrodinger_funext
    (ν k_sq ℏ : ℝ) (hℏ : ℏ ≠ 0) :
    (fun τ_E : ℝ => Real.exp (-((ℏ * ν * k_sq) / ℏ) * τ_E)) =
      (fun t : ℝ => Real.exp (-(ν * k_sq) * t)) := by
  funext s
  congr 2
  rw [show ℏ * ν * k_sq / ℏ = ν * k_sq from by field_simp]

/-- **Theorem: full ODE-level derivation of NS Stokes from Wick-rotated
Schrödinger.**

At the Madelung / Nelson identification `E_k = ℏ · ν · k²`, the
Wick-rotated Schrödinger eigen-ODE per Fourier mode is **the** NS Stokes
ODE for the same mode.  Both `HasDerivAt` statements assert
`df/ds = −(ν · k²) · f(s)`.

This is the ODE-level (dynamical) content behind the kernel-level identity
`ns_stokesKernel_eq_wickRotated_reversiblePhase`.  -/
lemma ns_stokes_ODE_eq_wickRotated_schrodinger_ODE (ν k_sq ℏ : ℝ)
    (hℏ : ℏ ≠ 0) :
    ∀ s : ℝ,
      HasDerivAt (fun τ_E : ℝ =>
          Real.exp (-((ℏ * ν * k_sq) / ℏ) * τ_E))
        (-(ν * k_sq) *
          Real.exp (-(ν * k_sq) * s)) s := by
  intro s
  rw [ns_stokes_eq_wickRotated_schrodinger_funext ν k_sq ℏ hℏ]
  exact ns_stokes_mode_satisfies_ODE ν k_sq s

/-!

The **Madelung–Nelson identification**

  `ν  =  ℏ / (2 m)`,

connects the NS kinematic viscosity `ν` to the reduced Planck constant
`ℏ` and the particle mass `m`.  Under this identification the **free
Schrödinger equation per Fourier mode** with energy `E_k = ℏ² k² /(2m)`
maps precisely onto the **NS Stokes equation per mode** with rate
constant `ν · k²`, via the previous ODE-level theorem
`ns_stokes_ODE_eq_wickRotated_schrodinger_ODE` at `E_k = ℏ · ν · k²`.

The Madelung polar decomposition `ψ = R · exp(i S/ℏ)` (in
`Physlib.QuantumMechanics.NonHermitian.WickRotation`) is the wave-function
layer this identification lives on.
-/

/-- **Madelung / Nelson kinematic viscosity** `ν = ℏ / (2m)` — identifying
NS viscosity with the Planck-mass ratio. -/
noncomputable def madelungViscosity (m hbar : ℝ) : ℝ := hbar / (2 * m)

/-- The Madelung viscosity is strictly positive when `m, ℏ > 0`. -/
lemma madelungViscosity_pos (m hbar : ℝ) (hm : 0 < m) (hℏ : 0 < hbar) :
    0 < madelungViscosity m hbar := by
  unfold madelungViscosity
  exact div_pos hℏ (by linarith)

/-- The Madelung viscosity matches `2 · m · ν = ℏ`. -/
lemma madelungViscosity_eq (m hbar : ℝ) (hm : m ≠ 0) :
    2 * m * madelungViscosity m hbar = hbar := by
  unfold madelungViscosity
  field_simp

/-- **Free-particle Schrödinger energy per Fourier mode** `E_k = ℏ² k²/(2m)`. -/
noncomputable def freeSchrodingerEnergyMode (m hbar k_sq : ℝ) : ℝ :=
  hbar ^ 2 * k_sq / (2 * m)

/-- **Madelung consistency:** the free-particle Schrödinger mode energy
satisfies `E_k = ℏ · ν · k²` with `ν` the Madelung viscosity.  This is the
exact rate-constant match required by
`ns_stokes_ODE_eq_wickRotated_schrodinger_ODE`. -/
lemma freeSchrodingerEnergyMode_eq_hbar_nu_k_sq
    (m hbar k_sq : ℝ) (hm : 0 < m) :
    freeSchrodingerEnergyMode m hbar k_sq =
      hbar * madelungViscosity m hbar * k_sq := by
  unfold freeSchrodingerEnergyMode madelungViscosity
  have hm_ne : m ≠ 0 := ne_of_gt hm
  field_simp

/-- **Madelung theorem: the free Schrödinger equation per mode is the NS
Stokes equation under `ν = ℏ/(2m)`.**

At the Madelung viscosity `ν = ℏ/(2m)`, the Wick-rotated free-particle
Schrödinger eigen-ODE per Fourier mode `k` with energy
`E_k = ℏ² k²/(2m)` is **literally** the NS Stokes ODE for the same mode
with rate constant `ν · k²`.  Both `HasDerivAt` statements assert
`df/ds = −(ν · k²) · f(s)` — the parabolic dissipative dynamics of NS
arise from Wick-rotating the unitary free Schrödinger evolution at the
Madelung-Nelson identification. -/
lemma madelung_freeSchrodinger_wick_eq_ns_stokes
    (m hbar k_sq : ℝ) (hm : 0 < m) (hℏ : 0 < hbar) :
    ∀ s : ℝ,
      HasDerivAt
        (fun τ_E : ℝ =>
          Real.exp
            (-(freeSchrodingerEnergyMode m hbar k_sq / hbar) * τ_E))
        (-(madelungViscosity m hbar * k_sq) *
          Real.exp
            (-(madelungViscosity m hbar * k_sq) * s)) s := by
  intro s
  -- Replace E_k with ℏ · ν · k² to align with the previous theorem.
  rw [freeSchrodingerEnergyMode_eq_hbar_nu_k_sq m hbar k_sq hm]
  exact ns_stokes_ODE_eq_wickRotated_schrodinger_ODE
    (madelungViscosity m hbar) k_sq hbar (ne_of_gt hℏ) s

/-!

The Madelung viscosity `ν = ℏ/(2m)` and the free-Schrödinger mode energy
`E_k = ℏ²·k²/(2m)` are dimensionally **kinematic viscosity** `[L²·T⁻¹]`
and **energy** `[M·L²·T⁻²]` respectively.  We restate the dimensional
identities from `Physlib.Units.WithDim.{Energy,Mass}` at the Madelung
layer, making the Madelung–Nelson identification structurally
typed in physlib's 6-base `{L, T, M, C, Θ, I}` basis.

The `I` (information) base is *not* visible in these mass / energy /
viscosity formulas — they live in the action sector.  The information
dimension enters separately through the imaginary action `S_I` via
`dimImaginaryAction_div_dimℏ_eq_I𝓭` (in `WithDim.Mass`).
-/

open Dimension.LTMCTI

/-- **Madelung viscosity is kinematic viscosity** `[L²·T⁻¹]`.
Dimensional restatement of `dimℏ_div_M𝓭_eq_L_sq_div_T` at the Madelung
layer: `[ν] = [ℏ]·[m⁻¹] = (M·L²·T⁻¹)·M⁻¹ = L²·T⁻¹`. -/
lemma madelungViscosity_dim_eq :
    dimℏ * M𝓭⁻¹ = L𝓭 * L𝓭 * T𝓭⁻¹ :=
  dimℏ_div_M𝓭_eq_L_sq_div_T

/-- **Free-Schrödinger mode energy has energy dimension** `[M·L²·T⁻²]`.

Computation: `[ℏ² · k² / m]
              = (M·L²·T⁻¹)² · L⁻² · M⁻¹
              = M²·L⁴·T⁻² · L⁻² · M⁻¹
              = M·L²·T⁻²
              = [E]`. -/
lemma freeSchrodingerEnergyMode_dim_eq :
    dimℏ * dimℏ * (L𝓭⁻¹ * L𝓭⁻¹) * M𝓭⁻¹ = dimEnergy := by
  ext b <;> cases b <;> simp [dimℏ, dimAction, dimEnergy] <;> ring

/-! ## Bisognano–Wichmann wedge KMS (Inoue, LNM 1699, §4.4–4.5)

The scalar shadow of the wedge standard system (Thm. 4.5.2), on one boost mode of energy `κ`. The real-time
flow `V(t) = reversiblePhaseC κ ℏ t = exp(−iκt/ℏ)` is the boost unitary group; its Wick rotation is the
Euclidean heat weight (`reversiblePhase_at_wickRotate`, already in this file); and:

* **Δ^{1/2} = V(iπ)** (Thm. 4.5.2(2)): the flow at half the Euclidean period squares to the wedge modular
  eigenvalue `Δ = e^{−2πκ/ℏ}` (`wedgeModular_sqrt_at_pi`, `wedgeModular_eq_boostFlow_two_pi`) — the modular
  operator is the analytic continuation of the boost to `iπ`.
* **the KMS boundary condition** (§4.4): shifting real time by one Euclidean period multiplies the flow by the
  Boltzmann weight, `f(t + iβℏ) = e^{−βκ}·f(t)` (`reversiblePhaseC_kms_shift`), with the `ThermalCircle`
  form `f(t + i·period) = matsubaraWeight·f(t)` (`reversiblePhaseC_kms_shift_thermalCircle`) reusing this
  file's `matsubaraWeight_eq_wickRotate`.
* **the modular conjugation reverses the flow** (Thm. 4.5.2(3)–(4)): complex conjugation sends `V(t)` to
  `V(−t)` (`reversiblePhaseC_conj`) — the antiunitary `J` maps the right-wedge flow to the left-wedge flow
  (`J𝒫(W_R)J = 𝒫(W_L)`); and the capstone `wedge_boost_wick_dichotomy` joins the unitary real-time flow, its
  Euclidean continuation, and `DampedHeatLandauerDichotomy.dampedHeat_two_sided_isometry_iff`: the analytic
  continuation is exactly the reversible → irreversible passage of the Landauer dichotomy.

Carriers cited but not imported (they sit downstream in `ComplexAction`): `KayWaldHawkingKMSHorizon`
(`hawkingBoltzmannWeight`, `kay_wald_stationary_kms`), `QuantumInertialFrameModularFromState`
(`modularGroupOfState_group_law`), `UnruhEntropicRate` (`lambdaU = a/(2πc)`). -/

/-- **The wedge modular eigenvalue** `Δ = e^{−2πκ/ℏ}` on a boost mode of energy `κ` — the Bisognano–Wichmann
modular operator of the Wightman wedge, at the level of one mode. -/
noncomputable def wedgeModularEigenvalue (κ ℏ : ℝ) : ℝ := Real.exp (-(2 * Real.pi * κ / ℏ))

/-- **[Δ is the boost continued to a full Euclidean period `2π`]** `Δ = V(wickRotate 2π)` — the wedge modular
eigenvalue is the boost flow analytically continued through one full period. -/
theorem wedgeModular_eq_boostFlow_two_pi (κ ℏ : ℝ) :
    (wedgeModularEigenvalue κ ℏ : ℂ) = reversiblePhaseC κ ℏ (wickRotate (2 * Real.pi)) := by
  rw [reversiblePhase_at_wickRotate, wedgeModularEigenvalue]
  norm_cast
  congr 1
  ring

/-- **[Δ^{1/2} = V(iπ), Inoue Thm. 4.5.2(2)]** the boost flow continued to the *half* period `π` squares to
the wedge modular eigenvalue: `V(wickRotate π)² = Δ`. The positive square root of the modular operator is the
boost at imaginary rapidity `iπ` — the heart of the Bisognano–Wichmann theorem. -/
@[zil_claim physlib.wedgeKms.modularSqrtAtPi,
  zil_concept physics.wedgeModularKms, zil_requires assumptions.singleBoostMode,
  zil_export]
theorem wedgeModular_sqrt_at_pi (κ ℏ : ℝ) :
    reversiblePhaseC κ ℏ (wickRotate Real.pi) ^ 2 = (wedgeModularEigenvalue κ ℏ : ℂ) := by
  rw [reversiblePhase_at_wickRotate, wedgeModularEigenvalue]
  norm_cast
  rw [sq, ← Real.exp_add]
  congr 1
  ring

/-- **[The complex phase is additive]** `V(z + w) = V(z)·V(w)` for all complex times — the flow is a
homomorphism on all of `ℂ`, so real-time evolution and Euclidean continuation compose freely. -/
lemma reversiblePhaseC_add (E ℏ : ℝ) (z w : ℂ) :
    reversiblePhaseC E ℏ (z + w) = reversiblePhaseC E ℏ z * reversiblePhaseC E ℏ w := by
  unfold reversiblePhaseC
  rw [← Complex.exp_add]
  congr 1
  ring

/-- **[The KMS boundary condition, Inoue §4.4]** shifting real time by one Euclidean period `iβℏ` multiplies
the flow by the Boltzmann weight: `V(t + wickRotate(ℏβ)) = e^{−βE}·V(t)`. This is the KMS analyticity
condition `ω(A σ_{iβ}(B)) = ω(BA)` at the level of one mode's correlation function. -/
@[zil_claim physlib.wedgeKms.kmsBoundaryShift,
  zil_concept physics.wedgeModularKms, zil_requires assumptions.nonzeroPlanck,
  zil_export]
theorem reversiblePhaseC_kms_shift (E ℏ β t : ℝ) (hℏ : ℏ ≠ 0) :
    reversiblePhaseC E ℏ ((t : ℂ) + wickRotate (ℏ * β)) =
      ((Real.exp (-(β * E)) : ℝ) : ℂ) * reversiblePhaseC E ℏ (t : ℂ) := by
  rw [reversiblePhaseC_add, reversiblePhase_at_wickRotate, mul_comm]
  rw [show E * (ℏ * β) / ℏ = β * E * (ℏ / ℏ) from by ring, div_self hℏ, mul_one]

/-- **[The KMS shift on a thermal circle]** `V(t + i·period) = matsubaraWeight·V(t)` — the KMS boundary
condition through this file's Matsubara carrier: one thermal period in imaginary time is exactly one
Boltzmann weight. -/
theorem reversiblePhaseC_kms_shift_thermalCircle (E t : ℝ) (T : ThermalCircle) :
    reversiblePhaseC E T.hbar ((t : ℂ) + wickRotate T.period) =
      matsubaraWeight E T * reversiblePhaseC E T.hbar (t : ℂ) := by
  rw [reversiblePhaseC_add, matsubaraWeight_eq_wickRotate, mul_comm]

/-- **[The modular conjugation reverses the flow, Inoue Thm. 4.5.2(3)–(4)]** complex conjugation sends `V(t)`
to `V(−t)`: the antiunitary part `J` of the Tomita operator maps the right-wedge boost flow to the left-wedge
flow — `J𝒫(W_R)J = 𝒫(W_L)`, at the level of one mode. -/
@[zil_claim physlib.wedgeKms.conjugationReversesFlow,
  zil_concept physics.wedgeModularKms, zil_requires assumptions.singleBoostMode,
  zil_export]
theorem reversiblePhaseC_conj (E ℏ t : ℝ) :
    starRingEnd ℂ (reversiblePhaseC E ℏ (t : ℂ)) = reversiblePhaseC E ℏ ((-t : ℝ) : ℂ) := by
  unfold reversiblePhaseC
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.conj_I]

/-- **[J is a genuine antiunitary implementing the wedge swap, Inoue Thm. 4.5.2(3)–(4)]** the modular
conjugation `J = starRingEnd ℂ` is isometric, involutive, and conjugates the boost flow to its reverse in the
operator sense `J V(t) J = V(−t)`: for every vector `z`, `J(V(t)·(J z)) = V(−t)·z`. This upgrades the scalar
identity `reversiblePhaseC_conj` to the antiunitary sandwich that maps the right-wedge dynamics to the
left-wedge dynamics. -/
@[zil_claim physlib.wedgeKms.conjugationAntiunitary,
  zil_concept physics.wedgeModularKms, zil_requires assumptions.singleBoostMode,
  zil_export]
theorem wedge_conjugation_antiunitary (E ℏ t : ℝ) :
    (∀ z : ℂ, ‖starRingEnd ℂ z‖ = ‖z‖)
    ∧ (∀ z : ℂ, starRingEnd ℂ (starRingEnd ℂ z) = z)
    ∧ (∀ z : ℂ, starRingEnd ℂ (reversiblePhaseC E ℏ (t : ℂ) * starRingEnd ℂ z)
        = reversiblePhaseC E ℏ ((-t : ℝ) : ℂ) * z) := by
  refine ⟨fun z => ?_, fun z => Complex.conj_conj z, fun z => ?_⟩
  · exact Complex.norm_conj z
  · rw [map_mul, reversiblePhaseC_conj, Complex.conj_conj]

zil_theorem_intent wedge_conjugation_antiunitary where
  at_level bridge_theorem
  must_mention [reversiblePhaseC, starRingEnd]

zil attach wedge_conjugation_antiunitary where
  formalizes @ "claim:modular-conjugation-is-antiunitary-wedge-swap",
  requires @ "claim:modular-conjugation-reverses-flow",
  supported_by @ "paper:inoue-tomita-takesaki-lnm1699",
  caveat @ "claim:single-mode-eigenvalue-not-operator-modular-theory"

/-- **[The real-time boost flow is unitary]** `‖V(t)‖ = 1` for every real `t` — the two-sided isometric
(modular-eligible) side of the dichotomy. -/
lemma reversiblePhaseC_norm_one (E ℏ t : ℝ) : ‖reversiblePhaseC E ℏ (t : ℂ)‖ = 1 := by
  unfold reversiblePhaseC
  rw [show -Complex.I * ((E / ℏ : ℝ) : ℂ) * (t : ℂ)
      = ((-(E / ℏ * t) : ℝ) : ℂ) * Complex.I from by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

/-- **[The damped propagator is the Wick-rotated boost]** `V(wickRotate t)` at unit `ℏ` and energy `m² + λ`
is exactly `damped_heat_propagator t` — the Euclidean/damped semigroup of the Landauer dichotomy *is* the
analytic continuation of the unitary boost flow. -/
theorem dampedHeat_is_wick_rotated_boost (m_sq lam t : ℝ) :
    reversiblePhaseC (m_sq + lam) 1 (wickRotate t) =
      ((damped_heat_propagator t m_sq lam : ℝ) : ℂ) := by
  rw [reversiblePhase_at_wickRotate]
  norm_cast
  unfold damped_heat_propagator
  congr 1
  ring

/-- **[The wedge dichotomy, assembled]** the Bisognano–Wichmann structure joined to the Landauer dichotomy:

* the real-time boost flow is unitary at every real time (`‖V(t)‖ = 1` — modular-eligible, reversible);
* its Wick rotation is the real damped heat weight (`V(wickRotate τ) = e^{−κτ/ℏ}`);
* and by `DampedHeatLandauerDichotomy.dampedHeat_two_sided_isometry_iff`, that damped side is two-sided
  isometric **iff** the rate vanishes.

The analytic continuation `t ↦ it` of Inoue Thm. 4.5.2 is exactly the reversible → irreversible passage: the
unitary (zero-entropy, Bennett) flow becomes the strictly contracting (erasing, Landauer) semigroup. -/
@[zil_claim physlib.wedgeKms.wickDichotomyBridge,
  zil_concept physics.irreversibilityDissipation, zil_requires assumptions.singleBoostMode,
  zil_export]
theorem wedge_boost_wick_dichotomy (κ ℏ m_sq lam : ℝ) :
    (∀ t : ℝ, ‖reversiblePhaseC κ ℏ (t : ℂ)‖ = 1)
    ∧ (∀ τ : ℝ, reversiblePhaseC κ ℏ (wickRotate τ) = ((Real.exp (-(κ * τ / ℏ)) : ℝ) : ℂ))
    ∧ ((∀ t : ℝ, |damped_heat_propagator t m_sq lam| = 1) ↔ m_sq + lam = 0) :=
  ⟨fun t => reversiblePhaseC_norm_one κ ℏ t,
   fun τ => reversiblePhase_at_wickRotate κ ℏ τ,
   dampedHeat_two_sided_isometry_iff m_sq lam⟩

/-! ### The Tomita operator on the doubled boost mode (Inoue Thm. 4.5.2(1)–(3))

The single-mode conjugation cannot invert `Δ` (a real scalar commutes with `conj`), so the honest carrier of
Tomita's polar decomposition is the **doubled** mode `ℂ × ℂ` — the right/left wedge pair (physically the
Unruh particle/antiparticle pair). There `Δ^{1/2}` weights the two members oppositely, `J` swaps and
conjugates them, and the three defining relations of Thm. 4.5.2 hold exactly:

* `S := J ∘ Δ^{1/2}` is an **involution** (`S² = 1` — Thm. 4.5.2(1): `S` is the closure of `AΩ ↦ A*Ω`);
* `J Δ^{1/2} J = Δ^{−1/2}` (the modular commutation, why the single mode could not carry it);
* `S* ∘ S = Δ` (the polar relation defining the modular operator), with `Δ` expressed through
  `wedgeModularEigenvalue` on each member. -/

/-- **`Δ^{1/2}` on the wedge pair** — `e^{−πκ/ℏ}` on the right member, `e^{+πκ/ℏ}` on the left: the two
wedges see reciprocal halves of the modular weight. -/
noncomputable def modularSqrtPair (κ ℏ : ℝ) (p : ℂ × ℂ) : ℂ × ℂ :=
  (((Real.exp (-(Real.pi * κ / ℏ)) : ℝ) : ℂ) * p.1,
   ((Real.exp (Real.pi * κ / ℏ) : ℝ) : ℂ) * p.2)

/-- **`J` on the wedge pair** — swap the wedges and conjugate: the antiunitary modular conjugation. -/
def wedgeConjugationPair (p : ℂ × ℂ) : ℂ × ℂ := (starRingEnd ℂ p.2, starRingEnd ℂ p.1)

/-- **The Tomita operator `S = J ∘ Δ^{1/2}`** on the wedge pair — the polar decomposition is the
definition. -/
noncomputable def tomitaSPair (κ ℏ : ℝ) : ℂ × ℂ → ℂ × ℂ :=
  wedgeConjugationPair ∘ modularSqrtPair κ ℏ

/-- **The adjoint Tomita operator `S* = Δ^{1/2} ∘ J`** (Thm. 4.5.2(3): `S* = JV(−iπ)`). -/
noncomputable def tomitaSStarPair (κ ℏ : ℝ) : ℂ × ℂ → ℂ × ℂ :=
  modularSqrtPair κ ℏ ∘ wedgeConjugationPair

/-- **The modular operator `Δ` on the wedge pair**, expressed through `wedgeModularEigenvalue`: the right
member carries `Δ(κ) = e^{−2πκ/ℏ}`, the left its reciprocal `Δ(−κ)`. -/
noncomputable def modularPair (κ ℏ : ℝ) (p : ℂ × ℂ) : ℂ × ℂ :=
  (((wedgeModularEigenvalue κ ℏ : ℝ) : ℂ) * p.1,
   ((wedgeModularEigenvalue (-κ) ℏ : ℝ) : ℂ) * p.2)

@[simp] lemma wedgeConjugationPair_involutive (p : ℂ × ℂ) :
    wedgeConjugationPair (wedgeConjugationPair p) = p := by
  unfold wedgeConjugationPair
  simp

/-- **[The modular commutation `J Δ^{1/2} J = Δ^{−1/2}`]** conjugation inverts the modular weight by
swapping the wedges — exactly the structure the single mode cannot carry. -/
theorem wedgeConjugation_modularSqrt_comm (κ ℏ : ℝ) (p : ℂ × ℂ) :
    wedgeConjugationPair (modularSqrtPair κ ℏ p)
      = modularSqrtPair (-κ) ℏ (wedgeConjugationPair p) := by
  unfold wedgeConjugationPair modularSqrtPair
  simp only [map_mul, Complex.conj_ofReal]
  ring_nf

/-- **[`S` is an involution, Thm. 4.5.2(1)] `S² = 1`** — the Tomita operator squares to the identity on the
wedge pair, as the closure of `AΩ ↦ A*Ω` must. -/
@[zil_claim physlib.wedgeKms.tomitaInvolution,
  zil_concept physics.wedgeModularKms, zil_requires assumptions.doubledBoostMode,
  zil_export]
theorem tomitaSPair_involutive (κ ℏ : ℝ) (p : ℂ × ℂ) :
    tomitaSPair κ ℏ (tomitaSPair κ ℏ p) = p := by
  unfold tomitaSPair wedgeConjugationPair modularSqrtPair
  simp only [Function.comp_apply, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  refine Prod.ext ?_ ?_ <;>
    · simp only [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, add_neg_cancel,
        neg_add_cancel, Real.exp_zero, Complex.ofReal_one, one_mul]

/-- **[The polar relation `S*S = Δ`]** the adjoint composed with the Tomita operator is the modular
operator — the defining equation of `Δ` in the polar decomposition `S = JΔ^{1/2}`. -/
@[zil_claim physlib.wedgeKms.tomitaPolarRelation,
  zil_concept physics.wedgeModularKms, zil_requires assumptions.doubledBoostMode,
  zil_export]
theorem tomitaSStar_comp_tomitaS (κ ℏ : ℝ) (p : ℂ × ℂ) :
    tomitaSStarPair κ ℏ (tomitaSPair κ ℏ p) = modularPair κ ℏ p := by
  unfold tomitaSStarPair tomitaSPair wedgeConjugationPair modularSqrtPair modularPair
    wedgeModularEigenvalue
  simp only [Function.comp_apply, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  refine Prod.ext ?_ ?_ <;>
    · simp only [← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
      congr 3
      ring

zil_theorem_intent tomitaSPair_involutive where
  at_level bridge_theorem
  must_mention [tomitaSPair]

zil_theorem_intent tomitaSStar_comp_tomitaS where
  at_level bridge_theorem
  must_mention [tomitaSStarPair, tomitaSPair, modularPair]

zil attach tomitaSPair_involutive where
  formalizes @ "claim:tomita-operator-is-involution",
  requires @ "assumption:doubled-boost-mode",
  supported_by @ "paper:inoue-tomita-takesaki-lnm1699",
  caveat @ "claim:doubled-mode-shadow-not-operator-modular-theory"

zil attach tomitaSStar_comp_tomitaS where
  formalizes @ "claim:tomita-polar-relation-s-star-s-eq-delta",
  requires @ "assumption:doubled-boost-mode",
  supported_by @ "paper:inoue-tomita-takesaki-lnm1699",
  supported_by @ "definition:wedge-modular-eigenvalue",
  caveat @ "claim:doubled-mode-shadow-not-operator-modular-theory"

zil attach wedgeConjugation_modularSqrt_comm where
  formalizes @ "claim:modular-commutation-j-delta-j-inverse",
  requires @ "assumption:doubled-boost-mode",
  supported_by @ "paper:inoue-tomita-takesaki-lnm1699"

/-! ### §F Toward full Tomita–Takesaki: the modular automorphism group, KMS, and the standard subspace

Three structural pillars beyond the polar decomposition, on the doubled boost mode:

* **the modular automorphism group `σ_t = Δ^{it}`** — a one-parameter *unitary* group, norm-preserving at
  **every** real time (unlike the damped semigroup), `modularFlowPair` with `modularFlowPair_group` /
  `modularFlowPair_unitary`;
* **the KMS condition** — shifting modular time by one imaginary unit multiplies the flow by the modular
  eigenvalue `Δ` (`modularFlow_kms_shift`), the defining equilibrium property, with the modular Hamiltonian
  energy `2πκ/ℏ` the Bisognano–Wichmann/Unruh `β = 2π` boost energy;
* **the standard real subspace** `K = {ξ : Sξ = ξ}` (`standardSubspacePair`) — the one-particle structure:
  `S` is additive and conjugate-homogeneous (`tomitaSPair_add`, `tomitaSPair_conj_smul`), hence `K` is
  **separating** (`K ∩ iK = {0}`, `standardSubspace_separating`) and **cyclic** (`K + iK` is everything,
  `standardSubspace_cyclic`).

This is the finite doubled-mode shadow of the standard form; it is not the infinite-dimensional GNS /
one-particle Hilbert space. -/

/-- The modular Hamiltonian eigenvalue `−log Δ = 2πκ/ℏ` — the Bisognano–Wichmann boost energy. -/
noncomputable def modularHamEigenvalue (κ ℏ : ℝ) : ℝ := 2 * Real.pi * κ / ℏ

/-- **The modular automorphism flow `σ_t = Δ^{it}` on the wedge pair** — `e^{−i(2πκ/ℏ)t}` on the right
member, its inverse on the left. A one-parameter unitary group. -/
noncomputable def modularFlowPair (κ ℏ t : ℝ) (p : ℂ × ℂ) : ℂ × ℂ :=
  (reversiblePhaseC (modularHamEigenvalue κ ℏ) 1 (t : ℂ) * p.1,
   reversiblePhaseC (-(modularHamEigenvalue κ ℏ)) 1 (t : ℂ) * p.2)

/-- **[`σ_0 = id`]** the modular flow at time zero is the identity. -/
@[simp] theorem modularFlowPair_zero (κ ℏ : ℝ) (p : ℂ × ℂ) :
    modularFlowPair κ ℏ 0 p = p := by
  unfold modularFlowPair reversiblePhaseC
  simp

/-- **[The modular flow is a one-parameter group] `σ_{s+t} = σ_s ∘ σ_t`.** -/
@[zil_claim physlib.wedgeKms.modularFlowGroup,
  zil_concept physics.wedgeModularKms, zil_requires assumptions.doubledBoostMode, zil_export]
theorem modularFlowPair_group (κ ℏ s t : ℝ) (p : ℂ × ℂ) :
    modularFlowPair κ ℏ (s + t) p = modularFlowPair κ ℏ s (modularFlowPair κ ℏ t p) := by
  unfold modularFlowPair
  refine Prod.ext ?_ ?_ <;>
    · push_cast
      rw [reversiblePhaseC_add, mul_assoc]

/-- **[The modular flow is unitary at every real time] `‖σ_t ξ‖ = ‖ξ‖`.** Both members are multiplied by
unit-modulus phases — the two-sided isometric structure the damped semigroup lacks. -/
@[zil_claim physlib.wedgeKms.modularFlowUnitary,
  zil_concept physics.irreversibilityDissipation, zil_requires assumptions.doubledBoostMode, zil_export]
theorem modularFlowPair_unitary (κ ℏ t : ℝ) (p : ℂ × ℂ) :
    ‖(modularFlowPair κ ℏ t p).1‖ = ‖p.1‖ ∧ ‖(modularFlowPair κ ℏ t p).2‖ = ‖p.2‖ := by
  unfold modularFlowPair
  constructor <;>
    · simp only [norm_mul, reversiblePhaseC_norm_one, one_mul]

/-- **[The KMS boundary condition] shifting modular time by one imaginary unit multiplies `σ_t` by `Δ`.**
`σ_{t+i}` equals `Δ · σ_t` on the right member — the defining KMS/equilibrium property of the modular flow,
`Δ = e^{−2πκ/ℏ}`. The modular Hamiltonian energy `2πκ/ℏ` is the Bisognano–Wichmann/Unruh `β = 2π` boost
energy. -/
@[zil_claim physlib.wedgeKms.modularFlowKms,
  zil_concept physics.wedgeModularKms, zil_requires assumptions.doubledBoostMode, zil_export]
theorem modularFlow_kms_shift (κ ℏ t : ℝ) :
    reversiblePhaseC (modularHamEigenvalue κ ℏ) 1 ((t : ℂ) + wickRotate 1)
      = (wedgeModularEigenvalue κ ℏ : ℂ) * reversiblePhaseC (modularHamEigenvalue κ ℏ) 1 (t : ℂ) := by
  have h := reversiblePhaseC_kms_shift (modularHamEigenvalue κ ℏ) 1 1 t one_ne_zero
  simp only [one_mul, mul_one] at h
  rw [h, wedgeModularEigenvalue, modularHamEigenvalue]

/-! #### The standard real subspace -/

/-- **[`S` is additive]** the Tomita operator preserves sums. -/
lemma tomitaSPair_add (κ ℏ : ℝ) (p q : ℂ × ℂ) :
    tomitaSPair κ ℏ (p + q) = tomitaSPair κ ℏ p + tomitaSPair κ ℏ q := by
  unfold tomitaSPair wedgeConjugationPair modularSqrtPair
  simp only [Function.comp_apply, Prod.fst_add, Prod.snd_add, mul_add, map_add, Prod.mk_add_mk]

/-- **[`S` is conjugate-homogeneous] `S(c ξ) = c̄ · Sξ`** — the Tomita operator is antilinear. -/
lemma tomitaSPair_conj_smul (κ ℏ : ℝ) (c : ℂ) (p : ℂ × ℂ) :
    tomitaSPair κ ℏ (c • p) = (starRingEnd ℂ c) • tomitaSPair κ ℏ p := by
  unfold tomitaSPair wedgeConjugationPair modularSqrtPair
  simp only [Function.comp_apply, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, map_mul,
    Complex.conj_ofReal, Prod.smul_mk]
  refine Prod.ext ?_ ?_ <;> · dsimp only; ring

/-- **[`S` on differences] `S(ξ − η) = Sξ − Sη`.** -/
lemma tomitaSPair_sub (κ ℏ : ℝ) (p q : ℂ × ℂ) :
    tomitaSPair κ ℏ (p - q) = tomitaSPair κ ℏ p - tomitaSPair κ ℏ q := by
  rw [sub_eq_add_neg, tomitaSPair_add, ← neg_one_smul ℂ q, tomitaSPair_conj_smul,
    map_neg, map_one, neg_one_smul, ← sub_eq_add_neg]

/-- **The standard real subspace** `K = {ξ : Sξ = ξ}` — the `+1` eigenspace of the Tomita involution `S`,
the one-particle structure of the wedge. -/
def standardSubspacePair (κ ℏ : ℝ) : Set (ℂ × ℂ) := {p | tomitaSPair κ ℏ p = p}

@[simp] lemma mem_standardSubspacePair (κ ℏ : ℝ) (p : ℂ × ℂ) :
    p ∈ standardSubspacePair κ ℏ ↔ tomitaSPair κ ℏ p = p := Iff.rfl

/-- **[The standard subspace is separating] `K ∩ iK = {0}`.** If both `ξ` and `iξ` are `S`-fixed then `ξ = 0`:
`S` is conjugate-linear, so `S(iξ) = −i Sξ = −iξ`, forcing `iξ = −iξ`. -/
@[zil_claim physlib.wedgeKms.standardSubspaceSeparating,
  zil_concept physics.wedgeModularKms, zil_requires assumptions.doubledBoostMode, zil_export]
theorem standardSubspace_separating (κ ℏ : ℝ) (p : ℂ × ℂ)
    (hp : p ∈ standardSubspacePair κ ℏ) (hip : Complex.I • p ∈ standardSubspacePair κ ℏ) :
    p = 0 := by
  rw [mem_standardSubspacePair, tomitaSPair_conj_smul, hp, Complex.conj_I] at hip
  have h2 : (Complex.I - (-Complex.I)) • p = 0 := by rw [sub_smul, hip, sub_self]
  rw [show Complex.I - (-Complex.I) = 2 * Complex.I from by ring] at h2
  rcases smul_eq_zero.mp h2 with h | h
  · exact absurd h (mul_ne_zero two_ne_zero Complex.I_ne_zero)
  · exact h

/-- **[The standard subspace is cyclic] `K + iK` is everything.** Every `p` decomposes as `ξ + iη` with
`ξ, η ∈ K`: take `ξ = ½(p + Sp)` and `η = −½i(p − Sp)`. -/
@[zil_claim physlib.wedgeKms.standardSubspaceCyclic,
  zil_concept physics.wedgeModularKms, zil_requires assumptions.doubledBoostMode, zil_export]
theorem standardSubspace_cyclic (κ ℏ : ℝ) (p : ℂ × ℂ) :
    ∃ ξ ∈ standardSubspacePair κ ℏ, ∃ η ∈ standardSubspacePair κ ℏ,
      p = ξ + Complex.I • η := by
  refine ⟨(2⁻¹ : ℂ) • (p + tomitaSPair κ ℏ p), ?_,
    (-(2⁻¹ : ℂ) * Complex.I) • (p - tomitaSPair κ ℏ p), ?_, ?_⟩
  · rw [mem_standardSubspacePair, tomitaSPair_conj_smul, tomitaSPair_add, tomitaSPair_involutive,
      map_inv₀, map_ofNat, add_comm (tomitaSPair κ ℏ p) p]
  · rw [mem_standardSubspacePair, tomitaSPair_conj_smul, tomitaSPair_sub, tomitaSPair_involutive]
    have hs : starRingEnd ℂ (-(2⁻¹ : ℂ) * Complex.I) = -(2⁻¹ : ℂ) * -Complex.I := by
      simp only [map_mul, map_neg, map_inv₀, map_ofNat, Complex.conj_I]
    rw [hs, show (p - tomitaSPair κ ℏ p) = -(tomitaSPair κ ℏ p - p) from (neg_sub _ _).symm,
      smul_neg, ← neg_smul]
    congr 1
    ring
  · have hI : Complex.I * (-(2⁻¹ : ℂ) * Complex.I) = 2⁻¹ := by
      have h : Complex.I * (-(2⁻¹ : ℂ) * Complex.I) = -(2⁻¹) * (Complex.I * Complex.I) := by ring
      rw [h, Complex.I_mul_I]; ring
    rw [smul_smul, hI]
    module

/-- **[The standard subspace is closed under differences]** `ξ₁, ξ₂ ∈ K ⟹ ξ₁ − ξ₂ ∈ K`. -/
lemma sub_mem_standardSubspacePair (κ ℏ : ℝ) {p q : ℂ × ℂ}
    (hp : p ∈ standardSubspacePair κ ℏ) (hq : q ∈ standardSubspacePair κ ℏ) :
    p - q ∈ standardSubspacePair κ ℏ := by
  rw [mem_standardSubspacePair, tomitaSPair_sub, hp, hq]

/-- **[The one-particle Reeh–Schlieder standard form] `K ⊕ iK = ℂ²`, uniquely.** Every vector decomposes as
`ξ + iη` with `ξ, η ∈ K` (**cyclic** — the vacuum reaches everything from the standard subspace), and the
decomposition is **unique** (**separating** — no nonzero vector is reachable two ways). Existence is
`standardSubspace_cyclic`; uniqueness is `standardSubspace_separating`. This is the vector-level form of the
Reeh–Schlieder cyclic-and-separating property that makes the Tomita operator well-defined. -/
@[zil_claim physlib.wedgeKms.standardSubspaceDirectSum,
  zil_concept physics.wedgeModularKms, zil_requires assumptions.doubledBoostMode, zil_export]
theorem standardSubspace_directSum (κ ℏ : ℝ) (p : ℂ × ℂ) :
    (∃ ξ ∈ standardSubspacePair κ ℏ, ∃ η ∈ standardSubspacePair κ ℏ, p = ξ + Complex.I • η)
      ∧ (∀ ξ₁ η₁ ξ₂ η₂ : ℂ × ℂ, ξ₁ ∈ standardSubspacePair κ ℏ → η₁ ∈ standardSubspacePair κ ℏ →
          ξ₂ ∈ standardSubspacePair κ ℏ → η₂ ∈ standardSubspacePair κ ℏ →
          ξ₁ + Complex.I • η₁ = ξ₂ + Complex.I • η₂ → ξ₁ = ξ₂ ∧ η₁ = η₂) := by
  refine ⟨standardSubspace_cyclic κ ℏ p, fun ξ₁ η₁ ξ₂ η₂ hξ₁ hη₁ hξ₂ hη₂ heq => ?_⟩
  have hvK : η₂ - η₁ ∈ standardSubspacePair κ ℏ := sub_mem_standardSubspacePair κ ℏ hη₂ hη₁
  have hEq2 : Complex.I • η₂ - Complex.I • η₁ = ξ₁ - ξ₂ := by
    rw [sub_eq_sub_iff_add_eq_add, add_comm (Complex.I • η₂) ξ₂]
    exact heq.symm
  have hivK : Complex.I • (η₂ - η₁) ∈ standardSubspacePair κ ℏ := by
    rw [smul_sub, hEq2]
    exact sub_mem_standardSubspacePair κ ℏ hξ₁ hξ₂
  have hv0 : η₂ - η₁ = 0 := standardSubspace_separating κ ℏ (η₂ - η₁) hvK hivK
  have hη : η₁ = η₂ := (sub_eq_zero.mp hv0).symm
  rw [hη] at heq
  exact ⟨add_right_cancel heq, hη⟩

/-! #### The modular two-point (Wightman) function and its KMS analyticity

The two-point function of the boost mode as a function of *complex* modular time `z`, `W(z) = e^{−i(2πκ/ℏ)z}`.
It is entire (a `Complex.exp`), so its real-time boundary values `W(t)` determine the analytic continuation
into the strip — the **edge-of-the-wedge** structure (Akhiezer, "The thin end of the wedge", 1973) — and the
**KMS boundary condition** is the value one imaginary modular period away: `W(t + i) = Δ·W(t)`, `Δ = e^{−2πκ/ℏ}`
the modular eigenvalue. The modular flow is KMS at modular inverse temperature `β = 1` (the physical Unruh
`β = 2π` sits inside the modular Hamiltonian energy `2πκ/ℏ`). -/

/-- **The modular two-point (Wightman) function** `W(z) = e^{−i(2πκ/ℏ)z}` of the boost mode, at complex modular
time `z` — an *entire* function whose real-time boundary values are the modular flow. -/
noncomputable def modularTwoPointFunction (κ ℏ : ℝ) (z : ℂ) : ℂ :=
  reversiblePhaseC (modularHamEigenvalue κ ℏ) 1 z

/-- **[The two-point function is multiplicative on complex time] `W(z+w) = W(z)·W(w)`** — the analyticity /
group structure inherited from `Complex.exp` (entire in `z`). -/
lemma modularTwoPointFunction_add (κ ℏ : ℝ) (z w : ℂ) :
    modularTwoPointFunction κ ℏ (z + w)
      = modularTwoPointFunction κ ℏ z * modularTwoPointFunction κ ℏ w :=
  reversiblePhaseC_add _ _ z w

/-- **[Real-time boundary values are unimodular] `‖W(t)‖ = 1`** — on the real axis the two-point function is a
pure phase (the unitary modular flow). -/
lemma modularTwoPointFunction_real_unitary (κ ℏ t : ℝ) :
    ‖modularTwoPointFunction κ ℏ (t : ℂ)‖ = 1 :=
  reversiblePhaseC_norm_one _ _ t

/-- **[The KMS boundary condition for the two-point function] `W(t + i) = Δ · W(t)`.** Continuing the modular
two-point function one imaginary modular period picks up the modular eigenvalue `Δ = e^{−2πκ/ℏ}` — the defining
equilibrium (KMS) analyticity of the boost-mode correlator. -/
@[zil_claim physlib.wedgeKms.kmsTwoPointBoundary,
  zil_concept physics.wedgeModularKms, zil_requires assumptions.doubledBoostMode, zil_export]
theorem modularTwoPointFunction_kms (κ ℏ t : ℝ) :
    modularTwoPointFunction κ ℏ ((t : ℂ) + wickRotate 1)
      = (wedgeModularEigenvalue κ ℏ : ℂ) * modularTwoPointFunction κ ℏ (t : ℂ) :=
  modularFlow_kms_shift κ ℏ t

/-- **[The KMS two-point function, assembled]** the boost-mode Wightman function is entire (multiplicative on
complex time), its real-time boundary values lie on the unit circle, and its value one imaginary modular period
away is `Δ` times the real-time value — the edge-of-the-wedge boundary data plus the KMS condition. -/
@[zil_claim physlib.wedgeKms.kmsTwoPointFunction,
  zil_concept physics.wedgeModularKms, zil_requires assumptions.doubledBoostMode, zil_export]
theorem modular_kms_two_point (κ ℏ t : ℝ) :
    (∀ z w : ℂ, modularTwoPointFunction κ ℏ (z + w)
        = modularTwoPointFunction κ ℏ z * modularTwoPointFunction κ ℏ w)
      ∧ ‖modularTwoPointFunction κ ℏ (t : ℂ)‖ = 1
      ∧ modularTwoPointFunction κ ℏ ((t : ℂ) + wickRotate 1)
          = (wedgeModularEigenvalue κ ℏ : ℂ) * modularTwoPointFunction κ ℏ (t : ℂ) :=
  ⟨modularTwoPointFunction_add κ ℏ, modularTwoPointFunction_real_unitary κ ℏ t,
   modularTwoPointFunction_kms κ ℏ t⟩

/-- **[The infinitesimal generator of the modular flow is the modular Hamiltonian] `dσ_t/dt|₀ = −iK`.** The
real-time derivative of the modular two-point function at `t = 0` is `−i` times the modular Hamiltonian energy
`K = 2πκ/ℏ` — the boost-mode shadow of `d/dt σ_t|₀ = ad_{−iK}` (`collisionStar`/`modularGenerator`). The
one-parameter modular flow is generated by the modular Hamiltonian. -/
@[zil_claim physlib.wedgeKms.modularFlowGenerator,
  zil_concept physics.wedgeModularKms, zil_requires assumptions.doubledBoostMode, zil_export]
theorem modularTwoPointFunction_generator (κ ℏ : ℝ) :
    HasDerivAt (fun t : ℝ => modularTwoPointFunction κ ℏ (t : ℂ))
      (-Complex.I * (modularHamEigenvalue κ ℏ : ℂ)) 0 := by
  have hlin : HasDerivAt
      (fun t : ℝ => -Complex.I * (modularHamEigenvalue κ ℏ : ℂ) * (t : ℂ))
      (-Complex.I * (modularHamEigenvalue κ ℏ : ℂ)) 0 := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul
      (-Complex.I * (modularHamEigenvalue κ ℏ : ℂ))
  simpa [modularTwoPointFunction, reversiblePhaseC, div_one, mul_assoc] using hlin.cexp

/-! ### Native ZIL claim graph and file contract -/

zil attach wedgeModular_sqrt_at_pi where
  formalizes @ "claim:wedge-modular-sqrt-is-boost-at-i-pi",
  supported_by @ "paper:inoue-tomita-takesaki-lnm1699",
  supported_by @ "paper:bisognano-wichmann-1975",
  caveat @ "claim:single-mode-eigenvalue-not-operator-modular-theory"

zil attach reversiblePhaseC_kms_shift where
  formalizes @ "claim:kms-boundary-shift-is-boltzmann-weight",
  requires @ "assumption:nonzero-planck",
  supported_by @ "paper:inoue-tomita-takesaki-lnm1699",
  supported_by @ "definition:matsubara-weight"

zil attach reversiblePhaseC_conj where
  formalizes @ "claim:modular-conjugation-reverses-flow",
  supported_by @ "paper:inoue-tomita-takesaki-lnm1699",
  caveat @ "claim:single-mode-eigenvalue-not-operator-modular-theory"

zil attach wedge_boost_wick_dichotomy where
  formalizes @ "claim:wick-rotation-is-reversible-to-irreversible-passage",
  requires @ "claim:damped-heat-two-sided-isometry-iff-zero-rate",
  supported_by @ "paper:inoue-tomita-takesaki-lnm1699",
  caveat @ "claim:scalar-shadow-not-operator-modular-theory"

zil_theorem_intent wedgeModular_sqrt_at_pi where
  at_level bridge_theorem
  must_mention [reversiblePhaseC, wickRotate, Real.pi, wedgeModularEigenvalue]

zil_theorem_intent reversiblePhaseC_kms_shift where
  at_level bridge_theorem
  must_mention [reversiblePhaseC, wickRotate, Real.exp]

zil_theorem_intent reversiblePhaseC_conj where
  at_level bridge_theorem
  must_mention [reversiblePhaseC, starRingEnd]

zil_theorem_intent wedge_boost_wick_dichotomy where
  at_level bridge_theorem
  must_mention [reversiblePhaseC, wickRotate, damped_heat_propagator]

zil_file_contract physlib.wedgeBoostModularKms where
  promises "On one boost mode, the Bisognano-Wichmann wedge structure holds in scalar shadow: the modular eigenvalue is the boost analytically continued through a full Euclidean period and its square root is the boost at i pi, shifting real time by one Euclidean period multiplies the flow by the Boltzmann (Matsubara) weight, complex conjugation reverses the flow (wedge swap), and the Wick rotation carries the unitary flow to the damped semigroup of the Landauer dichotomy."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.NonHermitian.WickRotation.reversiblePhaseC",
    "lean:Physlib.QFT.PathIntegral.wickRotate",
    "lean:Physlib.QFT.Matsubara.PathIntegral.matsubaraWeight",
    "lean:Physlib.QFT.PathIntegral.damped_heat_propagator",
    "lean:Physlib.QFT.PathIntegral.wedgeModularEigenvalue"]
  forbids_substitutes ["operator-algebraic Tomita-Takesaki theory claimed from scalar eigenvalue identities",
    "a wedge-local von Neumann algebra or cyclic-separating vacuum claim",
    "a dynamical identification of Wick rotation with physical dissipation"]
  witnessed_by [wedgeModular_sqrt_at_pi, reversiblePhaseC_kms_shift, reversiblePhaseC_conj,
    wedge_boost_wick_dichotomy]

#zil_formalization_lint physlib.wedgeBoostModularKms

/-! ### §F ZIL claim graph and contract — modular automorphism group + standard subspace -/

zil attach modularFlowPair_group where
  formalizes @ "claim:modular-flow-is-one-parameter-group",
  requires @ "assumption:doubled-boost-mode",
  supported_by @ "paper:inoue-tomita-takesaki-lnm1699"

zil attach modularFlowPair_unitary where
  supported_by @ "lean:Physlib.QFT.PathIntegral.reversiblePhaseC_norm_one",
  formalizes @ "claim:modular-flow-is-unitary-at-every-time",
  requires @ "assumption:doubled-boost-mode",
  caveat @ "claim:two-sided-isometry-contrasts-damped-semigroup"

zil attach modularFlow_kms_shift where
  formalizes @ "claim:modular-flow-satisfies-kms-at-modular-period",
  requires @ "assumption:doubled-boost-mode",
  supported_by @ "paper:inoue-tomita-takesaki-lnm1699",
  supported_by @ "definition:wedge-modular-eigenvalue"

zil attach standardSubspace_separating where
  formalizes @ "claim:standard-subspace-is-separating",
  requires @ "assumption:doubled-boost-mode",
  supported_by @ "definition:tomita-operator-conjugate-homogeneous",
  caveat @ "claim:finite-pair-shadow-not-gns-one-particle-space"

zil attach standardSubspace_cyclic where
  formalizes @ "claim:standard-subspace-is-cyclic",
  requires @ "assumption:doubled-boost-mode",
  supported_by @ "definition:tomita-operator-involution",
  caveat @ "claim:finite-pair-shadow-not-gns-one-particle-space"

zil attach standardSubspace_directSum where
  formalizes @ "claim:standard-subspace-reeh-schlieder-direct-sum",
  requires @ "claim:standard-subspace-is-cyclic",
  requires @ "claim:standard-subspace-is-separating",
  supported_by @ "paper:reeh-schlieder-1961",
  caveat @ "claim:finite-pair-shadow-not-gns-one-particle-space"

zil_theorem_intent standardSubspace_directSum where
  at_level bridge_theorem
  must_mention [standardSubspacePair]

zil attach modularTwoPointFunction_kms where
  formalizes @ "claim:modular-two-point-kms-boundary-condition",
  requires @ "assumption:doubled-boost-mode",
  supported_by @ "paper:akhiezer-1973",
  supported_by @ "definition:wedge-modular-eigenvalue"

zil attach modular_kms_two_point where
  formalizes @ "claim:modular-kms-two-point-function-assembled",
  requires @ "claim:modular-two-point-kms-boundary-condition",
  supported_by @ "paper:akhiezer-1973",
  supported_by @ "paper:inoue-tomita-takesaki-lnm1699",
  caveat @ "claim:entire-boundary-data-not-full-edge-of-wedge-theorem"

zil_theorem_intent modularTwoPointFunction_kms where
  at_level bridge_theorem
  must_mention [modularTwoPointFunction, wedgeModularEigenvalue, wickRotate]

zil_theorem_intent modular_kms_two_point where
  at_level bridge_theorem
  must_mention [modularTwoPointFunction, wedgeModularEigenvalue, wickRotate]

zil attach modularTwoPointFunction_generator where
  formalizes @ "claim:modular-flow-generator-is-modular-hamiltonian",
  requires @ "assumption:doubled-boost-mode",
  supported_by @ "definition:modular-hamiltonian-eigenvalue",
  caveat @ "claim:scalar-generator-not-operator-ad-k"

zil_theorem_intent modularTwoPointFunction_generator where
  at_level bridge_theorem
  must_mention [modularTwoPointFunction, modularHamEigenvalue]

zil_theorem_intent modularFlowPair_group where
  at_level bridge_theorem
  must_mention [modularFlowPair]

zil_theorem_intent modularFlowPair_unitary where
  at_level bridge_theorem
  must_mention [modularFlowPair]

zil_theorem_intent modularFlow_kms_shift where
  at_level bridge_theorem
  must_mention [reversiblePhaseC, modularHamEigenvalue, wedgeModularEigenvalue, wickRotate]

zil_theorem_intent standardSubspace_separating where
  at_level bridge_theorem
  must_mention [standardSubspacePair]

zil_theorem_intent standardSubspace_cyclic where
  at_level bridge_theorem
  must_mention [standardSubspacePair]

zil_file_contract physlib.modularAutomorphismStandardSubspace where
  promises "On the doubled boost mode the three remaining Tomita-Takesaki pillars hold in finite shadow: the modular flow is a one-parameter unitary group, it satisfies the KMS boundary condition at the modular period (picking up the modular eigenvalue Delta), and the standard real subspace of S-fixed vectors is both separating and cyclic."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QFT.PathIntegral.modularFlowPair",
    "lean:Physlib.QFT.PathIntegral.modularHamEigenvalue",
    "lean:Physlib.QFT.PathIntegral.tomitaSPair",
    "lean:Physlib.QFT.PathIntegral.standardSubspacePair",
    "lean:Physlib.QFT.PathIntegral.wedgeModularEigenvalue"]
  forbids_substitutes ["an infinite-dimensional GNS or one-particle Hilbert space claim",
    "operator-algebraic Tomita-Takesaki theory claimed from the finite pair shadow",
    "a claim that the finite standard subspace generates a von Neumann algebra"]
  witnessed_by [modularFlowPair_group, modularFlowPair_unitary, modularFlow_kms_shift,
    standardSubspace_separating, standardSubspace_cyclic, standardSubspace_directSum]

#zil_formalization_lint physlib.modularAutomorphismStandardSubspace

zil_file_contract physlib.modularKmsTwoPoint where
  promises "The boost-mode modular two-point (Wightman) function is entire in complex modular time (multiplicative), its real-time boundary values are unimodular, and its value one imaginary modular period away is the modular eigenvalue Delta times the real-time value — the edge-of-the-wedge boundary data plus the KMS equilibrium condition."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QFT.PathIntegral.modularTwoPointFunction",
    "lean:Physlib.QFT.PathIntegral.wedgeModularEigenvalue",
    "lean:Physlib.QFT.PathIntegral.wickRotate"]
  forbids_substitutes ["a full edge-of-the-wedge analytic-continuation theorem from the entire boundary data",
    "a Wightman two-point function of an interacting quantum field",
    "an operator-algebraic KMS state claim from the scalar correlator"]
  witnessed_by [modularTwoPointFunction_kms, modular_kms_two_point,
    modularTwoPointFunction_generator]

#zil_formalization_lint physlib.modularKmsTwoPoint

end Physlib.QFT.PathIntegral

end

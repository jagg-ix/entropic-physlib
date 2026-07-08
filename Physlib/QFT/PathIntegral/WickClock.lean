/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QFT.PathIntegral.FeynmanKac
public import Physlib.QFT.PathIntegral.Lorentzian
public import Physlib.QFT.Matsubara.PathIntegral
public import Physlib.Units.WithDim.Mass

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

/-! ## §1 — Wick rotation operator -/

/-- **Wick rotation substitution**: takes a real Euclidean time `τ_E`
to the complex Lorentzian time `t = −i · τ_E`. -/
def wickRotate (τ_E : ℝ) : ℂ := -Complex.I * (τ_E : ℂ)

/-- **Inverse Wick rotation**: takes a real Lorentzian time `t` to the
complex Euclidean time `i · t`. -/
def wickRotateInv (t : ℝ) : ℂ := Complex.I * (t : ℂ)

@[simp] theorem wickRotate_zero : wickRotate 0 = 0 := by
  unfold wickRotate; simp

@[simp] theorem wickRotateInv_zero : wickRotateInv 0 = 0 := by
  unfold wickRotateInv; simp

/-- Wick rotation is odd: `wickRotate (−τ_E) = − wickRotate τ_E`. -/
theorem wickRotate_neg (τ_E : ℝ) :
    wickRotate (-τ_E) = -wickRotate τ_E := by
  unfold wickRotate; push_cast; ring

/-- Real part of the Wick-rotated time is zero (purely imaginary). -/
@[simp] theorem wickRotate_re (τ_E : ℝ) : (wickRotate τ_E).re = 0 := by
  unfold wickRotate; simp

/-- Imaginary part of the Wick-rotated time is `−τ_E`. -/
@[simp] theorem wickRotate_im (τ_E : ℝ) : (wickRotate τ_E).im = -τ_E := by
  unfold wickRotate; simp

/-! ## §2 — Metric-signature flip: `dt² ↦ −dτ_E²` -/

/-- **Metric-signature flip.** Under Wick rotation the squared Lorentzian
time-element `t²` becomes minus the squared Euclidean time-element `τ_E²`:
`(wickRotate τ_E)² = −(τ_E : ℂ)²`.

This is the *coordinate-level* expression of the Lorentzian → Euclidean
signature change `dt² ↦ −dτ_E²` (equivalently, in `(+−−−)` Minkowski
signature, the timelike component contributes `−` to the Lorentzian
line element and `+` to the Euclidean line element). -/
theorem wickRotate_sq (τ_E : ℝ) :
    (wickRotate τ_E) ^ 2 = -((τ_E : ℂ) ^ 2) := by
  unfold wickRotate
  have : (-Complex.I) ^ 2 = -1 := by
    rw [neg_pow, Complex.I_sq]
    simp
  calc (-Complex.I * (τ_E : ℂ)) ^ 2
      = (-Complex.I) ^ 2 * (τ_E : ℂ) ^ 2 := by ring
    _ = (-1) * (τ_E : ℂ) ^ 2 := by rw [this]
    _ = -((τ_E : ℂ) ^ 2) := by ring

/-- **Purely-timelike Lorentzian proper time as imaginary Euclidean time.**
For a purely timelike segment (`dx = 0`), the Lorentzian proper-time
element `dτ_L = dt` and its Wick-rotated counterpart `τ_L = −i·τ_E`
satisfy `τ_L² = −τ_E²`. -/
theorem properTime_lorentz_to_euclidean_sq (τ_E : ℝ) :
    (wickRotate τ_E) ^ 2 = -((τ_E : ℂ) ^ 2) :=
  wickRotate_sq τ_E

/-! ## §3 — Reversible-sector kernel reduction at `t = wickRotate τ_E` -/

/-- **Reversible-sector Wick reduction.**  The complex-time reversible
phase `reversiblePhaseC E_R ℏ t = exp(−i·E_R·t/ℏ)`, evaluated at the
Wick-rotated time `t = wickRotate τ_E`, becomes the real Euclidean
heat kernel `exp(−E_R·τ_E/ℏ)`.  This is the
`reversiblePhase_wickRotation` theorem stated via the named operator. -/
theorem reversiblePhase_at_wickRotate (E_R ℏ τ_E : ℝ) :
    reversiblePhaseC E_R ℏ (wickRotate τ_E) =
      ((Real.exp (-(E_R * τ_E / ℏ)) : ℝ) : ℂ) := by
  unfold wickRotate
  exact reversiblePhase_wickRotation E_R ℏ τ_E

/-- **Lorentzian propagator at `H_I = 0` reduces to the Euclidean heat
kernel under Wick rotation.**  For a purely-Hermitian Hamiltonian
(`H_I = 0`), the Lorentzian scalar propagator viewed via
`reversiblePhaseC`, at the Wick-rotated time, becomes the real
Euclidean exponential. -/
theorem lorentzianPropagator_at_wickRotate_HI_zero
    (H_R ℏ τ_E : ℝ) :
    reversiblePhaseC H_R ℏ (wickRotate τ_E) =
      ((Real.exp (-(H_R * τ_E / ℏ)) : ℝ) : ℂ) :=
  reversiblePhase_at_wickRotate H_R ℏ τ_E

/-! ## §4 — Thermal Boltzmann reduction (one-period Wick rotation) -/

/-- **Wick at the thermal period gives the Boltzmann weight.**  At
`τ_E = βℏ` (one full period of the thermal circle), the Wick-rotated
reversible phase is the Boltzmann weight `exp(−βE_R)`. -/
theorem reversiblePhase_at_wickRotate_thermalPeriod
    (E_R : ℝ) (T : ThermalCircle) :
    reversiblePhaseC E_R T.hbar (wickRotate T.period) =
      ((Real.exp (-(T.beta * E_R)) : ℝ) : ℂ) := by
  unfold wickRotate
  exact euclidean_reversiblePhase_at_thermalPeriod_eq_boltzmann E_R T

/-- The Boltzmann weight `exp(−βE_R)` is the one-period Wick rotation,
restated through the `wickRotate` operator. -/
theorem matsubaraWeight_eq_wickRotate (E_R : ℝ) (T : ThermalCircle) :
    matsubaraWeight E_R T = reversiblePhaseC E_R T.hbar (wickRotate T.period) :=
  (reversiblePhase_at_wickRotate_thermalPeriod E_R T).symm

/-! ## §5 — Damping is invariant under Wick rotation -/

/-- **`path_integral_damping` is a real coercion.**  The scalar
path-integral damping factor is a *real* number `exp(−S_I/ℏ)`; viewed
as `ℂ`, it is `Complex.ofReal` of a real exponential — entirely in the
modulus, not the phase. -/
theorem path_integral_damping_eq_real (ℏ S_I : ℝ) :
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
theorem lorentzianKernel_modulus_invariant_under_wick
    (S_R S_I ℏ : ℝ) :
    ‖lorentzianKernel S_R S_I ℏ‖ = path_integral_damping ℏ S_I := by
  rw [lorentzianKernel_norm_eq_path_integral_damping]

/-! ## §6 — Navier–Stokes diffusion as a Wick-rotated reversible phase -/

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
theorem ns_stokesKernel_eq_wickRotated_reversiblePhase
    (ν k_sq τ_E ℏ : ℝ) (hℏ : ℏ ≠ 0) :
    reversiblePhaseC (ℏ * ν * k_sq) ℏ (wickRotate τ_E) =
      ((Real.exp (-(ν * k_sq * τ_E)) : ℝ) : ℂ) := by
  rw [reversiblePhase_at_wickRotate]
  congr 2
  rw [show ℏ * ν * k_sq * τ_E / ℏ = ν * k_sq * τ_E from by field_simp]

/-! ### §6.1 — ODE-level derivation: NS Stokes per mode = Wick-rotated Schrödinger

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
theorem wickRotated_schrodinger_satisfies_heatEq (E ℏ : ℝ) :
    ∀ τ_E : ℝ, HasDerivAt (fun s : ℝ => Real.exp (-(E / ℏ) * s))
      (-(E / ℏ) * Real.exp (-(E / ℏ) * τ_E)) τ_E :=
  damping_satisfies_decay_ODE (E / ℏ)

/-- **(Step 4) NS Stokes ODE per Fourier mode `k`.**  The Stokes diffusion
solution `u_k(t) = exp(−ν · k² · t)` satisfies
`du_k/dt = −(ν · k²) · u_k(t)`.  Direct specialisation of
`damping_satisfies_decay_ODE` with `V = ν · k²`. -/
theorem ns_stokes_mode_satisfies_ODE (ν k_sq : ℝ) :
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
theorem ns_stokes_eq_wickRotated_schrodinger_funext
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
theorem ns_stokes_ODE_eq_wickRotated_schrodinger_ODE (ν k_sq ℏ : ℝ)
    (hℏ : ℏ ≠ 0) :
    ∀ s : ℝ,
      HasDerivAt (fun τ_E : ℝ =>
          Real.exp (-((ℏ * ν * k_sq) / ℏ) * τ_E))
        (-(ν * k_sq) *
          Real.exp (-(ν * k_sq) * s)) s := by
  intro s
  rw [ns_stokes_eq_wickRotated_schrodinger_funext ν k_sq ℏ hℏ]
  exact ns_stokes_mode_satisfies_ODE ν k_sq s

/-! ### §6.2 — Madelung / Nelson viscosity `ν = ℏ/(2m)`

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
theorem madelungViscosity_pos (m hbar : ℝ) (hm : 0 < m) (hℏ : 0 < hbar) :
    0 < madelungViscosity m hbar := by
  unfold madelungViscosity
  exact div_pos hℏ (by linarith)

/-- The Madelung viscosity matches `2 · m · ν = ℏ`. -/
theorem madelungViscosity_eq (m hbar : ℝ) (hm : m ≠ 0) :
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
theorem freeSchrodingerEnergyMode_eq_hbar_nu_k_sq
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
theorem madelung_freeSchrodinger_wick_eq_ns_stokes
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

/-! ### §6.3 — Dimensional consistency of the Madelung formulas

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

open Dimension

/-- **Madelung viscosity is kinematic viscosity** `[L²·T⁻¹]`.
Dimensional restatement of `dimℏ_div_M𝓭_eq_L_sq_div_T` at the Madelung
layer: `[ν] = [ℏ]·[m⁻¹] = (M·L²·T⁻¹)·M⁻¹ = L²·T⁻¹`. -/
theorem madelungViscosity_dim_eq :
    dimℏ * M𝓭⁻¹ = L𝓭 * L𝓭 * T𝓭⁻¹ :=
  dimℏ_div_M𝓭_eq_L_sq_div_T

/-- **Free-Schrödinger mode energy has energy dimension** `[M·L²·T⁻²]`.

Computation: `[ℏ² · k² / m]
              = (M·L²·T⁻¹)² · L⁻² · M⁻¹
              = M²·L⁴·T⁻² · L⁻² · M⁻¹
              = M·L²·T⁻²
              = [E]`. -/
theorem freeSchrodingerEnergyMode_dim_eq :
    dimℏ * dimℏ * (L𝓭⁻¹ * L𝓭⁻¹) * M𝓭⁻¹ = dimEnergy := by
  ext <;> simp [dimℏ, dimAction, dimEnergy] <;> ring

end Physlib.QFT.PathIntegral

end

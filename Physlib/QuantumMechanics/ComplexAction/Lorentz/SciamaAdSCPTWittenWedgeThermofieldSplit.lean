/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTUnruhFourClocks
public import Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.Basic
public import Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SplitPropertyStatisticalIndependence
meta import Zil

/-!
# The fundamental example completed: the vacuum as wedge thermofield double, and factorized states
(Witten, arXiv:1803.04993 §5.1–5.2, §7)

Continues the Witten arc using the four-clock reading (`SciamaAdSCPTUnruhFourClocks`): the remaining §5
content — the Minkowski vacuum as the **thermofield double** of the two Rindler wedges, prepared by the
Euclidean path integral — and §7's factorization/split question.

* **§5.1 — the vacuum is the wedge thermofield double** (`tfd_halfweight_sq_is_unruh`): the TFD amplitude
  `e^{−β_UE/2}` (`ThermoFieldDynamics.Basic.thermalWeight`) **squares to the wedge-modular eigenvalue** at the
  Unruh inverse temperature — tracing out one wedge of the TFD gives the thermal weight the accelerated
  observer sees.  This is the Page–Wootters leverage made exact: the global vacuum is the *entangled clock–
  system pair* (left wedge = clock, right wedge = system), and conditioning on one side yields the thermal
  state of the other.
* **§5.2 — the Euclidean path integral prepares it** (`tfd_amplitude_is_sqrt_wedgeModular` +
  `euclidean_half_rotation_squares_to_modular`): the TFD amplitude **is** `√Δ`, and the Euclidean boost
  rotation by `π` — half the full `2π` rotation of the four-clock reading — squares to the modular eigenvalue,
  `V(iπ)² = Δ` (`WickClock.wedgeModular_sqrt_at_pi`): the path integral over half the Euclidean plane prepares
  the vacuum as the TFD with amplitude `Δ^{1/2}`, Witten's §5.2 in eigenvalue form.
* **§5.1's kinematics** (`tfd_left_right_commute`, reused): the left and right wedge actions commute
  (`mulLeft`/`mulRight`) — the two commuting wedge algebras of the Haag-dual split, the kinematic precondition
  for the TFD/Page–Wootters pair.
* **§7 — factorized states from the split property** (`split_statistical_independence`, reused; bundled in the
  capstone): in Type III the global Hilbert space does *not* factorize across a sharp wedge split (the §6 trace
  obstruction); the **split property** — an interpolating type I factor across a corridor — restores
  statistical independence `ab = ba`, the algebraic core of a tensor factorization: Witten's §7 question and
  its standard resolution, on the repo's local net.

`witten_wedge_thermofield_split_synthesis` bundles the storyline: the vacuum is the wedge TFD (thermal at
`T_U` by the four clocks), its amplitude is `√Δ` prepared by the Euclidean half-rotation, the two wedge
actions commute, and factorization across a corridor is restored by the split property.

Honest scope: eigenvalue/amplitude-level identities (matching the wedge arc) plus exact reuse of the TFD and
split machinery; the continuum §5 (Bisognano–Wichmann operator form) and the §7 corridor construction are the
cited counterparts.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTWittenWedgeThermofieldSplit

open Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTUnruhFourClocks
open Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.Basic
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SplitPropertyStatisticalIndependence
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.StarAlgebraGNSFormCommutant
open Physlib.QuantumMechanics.ComplexAction.AlgebraicQFTQuasifree.HadamardLocalNet
open Physlib.QFT.PathIntegral
open Physlib.QuantumMechanics.NonHermitian.WickRotation
open Physlib.Thermodynamics

/-! ## §1. The vacuum is the wedge thermofield double (Witten §5.1) -/

/-- **[The TFD half-weight squares to the wedge-modular eigenvalue]** `(e^{−β_UE/2})² = Δ = e^{−2πκ/ℏ}` at
`κ = cE/a` — the thermofield-double amplitude at the Unruh inverse temperature squares to the wedge eigenvalue:
tracing out one wedge of the TFD vacuum gives exactly the thermal weight the accelerated observer sees.  The
Page–Wootters pair made exact: left wedge = clock, right wedge = system, conditioning = thermality. -/
theorem tfd_halfweight_sq_is_unruh (ℏ kB c a E : ℝ)
    (hℏ : ℏ ≠ 0) (hkB : kB ≠ 0) (hc : c ≠ 0) (ha : a ≠ 0) :
    thermalWeight (1 / (kB * unruhTemperature ℏ kB c a)) E ^ 2
      = wedgeModularEigenvalue (c * E / a) ℏ := by
  rw [thermalWeight_sq]
  show Real.exp _ = Real.exp _
  congr 1
  unfold unruhTemperature
  field_simp

/-! ## §2. The Euclidean path integral prepares the TFD (Witten §5.2) -/

/-- **[The TFD amplitude is `√Δ`]** — the thermofield-double half-weight is the square root of the
wedge-modular eigenvalue: the Euclidean preparation amplitude of the vacuum across the wedge split. -/
theorem tfd_amplitude_is_sqrt_wedgeModular (ℏ kB c a E : ℝ)
    (hℏ : ℏ ≠ 0) (hkB : kB ≠ 0) (hc : c ≠ 0) (ha : a ≠ 0) :
    Real.sqrt (wedgeModularEigenvalue (c * E / a) ℏ)
      = thermalWeight (1 / (kB * unruhTemperature ℏ kB c a)) E := by
  rw [← tfd_halfweight_sq_is_unruh ℏ kB c a E hℏ hkB hc ha]
  exact Real.sqrt_sq (Real.exp_pos _).le

/-- **[The Euclidean half-rotation squares to the modular eigenvalue]** `V(iπ)² = Δ` — the boost rotated to
imaginary rapidity `iπ` (half the full `2π` Euclidean rotation of the four-clock reading) squares to the
wedge-modular eigenvalue (`WickClock.wedgeModular_sqrt_at_pi`): the path integral over half the Euclidean
plane prepares the vacuum as the TFD with amplitude `Δ^{1/2}`. -/
theorem euclidean_half_rotation_squares_to_modular (κ ℏ : ℝ) :
    reversiblePhaseC κ ℏ (wickRotate Real.pi) ^ 2 = (wedgeModularEigenvalue κ ℏ : ℂ) :=
  wedgeModular_sqrt_at_pi κ ℏ

/-! ## §3. The synthesis: wedge TFD, Euclidean preparation, commuting wedges, split factorization -/

/-- **[The fundamental example and factorized states, bundled]** — **(i)** the vacuum is the wedge TFD: the
half-weight squares to the Unruh/wedge eigenvalue; **(ii)** its amplitude is `√Δ`, prepared by the Euclidean
half-rotation `V(iπ)² = Δ`; **(iii)** the left and right wedge actions commute (the Haag-dual kinematics of
the TFD/Page–Wootters pair); **(iv)** across a split corridor, region and outer-complement observables are
statistically independent (`ab = ba`) — the algebraic core of the §7 factorization, restored by the split
property in a theory whose sharp-split algebras are Type III (§6). -/
theorem witten_wedge_thermofield_split_synthesis {n : ℕ} (Hm : Matrix (Fin n) (Fin n) ℂ)
    {A ι : Type*} [Monoid A] {Preι : Preorder ι} (N : LocalNet A ι) {O O₁ : ι}
    (hsplit : HasSplitProperty N O O₁)
    (ℏ kB c a E κ : ℝ) (hℏ : ℏ ≠ 0) (hkB : kB ≠ 0) (hc : c ≠ 0) (ha : a ≠ 0) :
    thermalWeight (1 / (kB * unruhTemperature ℏ kB c a)) E ^ 2
        = wedgeModularEigenvalue (c * E / a) ℏ
      ∧ reversiblePhaseC κ ℏ (wickRotate Real.pi) ^ 2 = (wedgeModularEigenvalue κ ℏ : ℂ)
      ∧ (LinearMap.mulLeft ℂ Hm).comp (LinearMap.mulRight ℂ Hm)
          = (LinearMap.mulRight ℂ Hm).comp (LinearMap.mulLeft ℂ Hm)
      ∧ (∀ x ∈ N.alg O, ∀ y ∈ commutant (N.alg O₁), x * y = y * x) :=
  ⟨tfd_halfweight_sq_is_unruh ℏ kB c a E hℏ hkB hc ha,
    wedgeModular_sqrt_at_pi κ ℏ,
    tfd_left_right_commute Hm,
    fun x hx y hy => split_statistical_independence hsplit x hx y hy⟩

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTWittenWedgeThermofieldSplit

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTWittenWedgeThermofieldSplit.tfd_halfweight_sq_is_unruh where
  formalizes @ "claim:the-thermofield-double-half-weight-at-the-unruh-temperature-squares-to-the-wedge-modular-eigenvalue",
  requires @ "claim:the-unruh-boltzmann-weight-equals-the-wedge-modular-eigenvalue-at-boost-parameter-c-e-over-a",
  supported_by @ "paper:witten-2018-notes-on-some-entanglement-properties-of-quantum-field-theory",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ThermoFieldDynamics.Basic.thermalWeight",
  caveat @ "epistemic:eigenvalue-amplitude-level-the-operator-bisognano-wichmann-remains-the-graph-assumption"

zil attach Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTWittenWedgeThermofieldSplit.witten_wedge_thermofield_split_synthesis where
  formalizes @ "claim:the-vacuum-is-the-wedge-thermofield-double-prepared-by-the-euclidean-half-rotation-with-factorization-restored-by-the-split-property",
  requires @ "claim:the-thermofield-double-half-weight-at-the-unruh-temperature-squares-to-the-wedge-modular-eigenvalue",
  supported_by @ "paper:witten-2018-notes-on-some-entanglement-properties-of-quantum-field-theory",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.AlgebraicQFT.SplitPropertyStatisticalIndependence.split_statistical_independence",
  supported_by @ "lean:Physlib.QFT.PathIntegral.wedgeModular_sqrt_at_pi",
  caveat @ "epistemic:the-continuum-corridor-construction-and-type-classification-are-cited-counterparts"

/- ZIL-END -/

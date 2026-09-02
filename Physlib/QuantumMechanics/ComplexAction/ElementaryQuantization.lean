/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.Analysis.Real.Sqrt

/-!
# Three elementary quantization conditions

Three textbook quantization results, from first principles.

* **§A Charge quantization.** A state that picks up the phase `e^{iqθ}` under a `U(1)` gauge rotation
  `θ` must be single-valued as `θ` sweeps a full circle `θ → θ + 2π`; this forces `e^{2πiq} = 1`, which
  holds **iff** the charge `q` is an integer (`charge_single_valued_iff_int`). Integer charges are closed
  under addition (`charge_add_quantized`). This is the origin of the integer electric charge that the
  winding/ribbon-twist arc takes as given (`Hopf.ChargeConjugationRibbonTwist.chargeState (q : ℤ)`,
  `Winding.QuarkChargeWinding.windingCharge`); here `q` is that winding number.
* **§B Free massive Klein–Gordon evolution.** The relativistic dispersion `ω(k) = √(k² + m²)`
  (`kgFrequency`) is the positive mass-shell energy: `ω² = k² + m²` (`kgFrequency_sq`), equivalently
  `ω² − k² = m²` (`kg_massShell`, the Lorentz-invariant `E² − p² = m²`; cf. the ADM form
  `SpacetimePositiveMass.admMass = √(E² − P²)`). The rest energy `|m|` is the floor
  (`kgFrequency_ge_mass`, attained at `k = 0`, `kgFrequency_at_zero`). The temporal mode `e^{−iωt}`
  (`kgMode`) evolves as a one-parameter unitary group — `‖·‖ = 1` (`kgMode_unitary`), `U(0) = 1`
  (`kgMode_zero`), `U(t+s) = U(t)U(s)` (`kgMode_add`) — and the group velocity `dω/dk = k/ω`
  (`kgGroupVelocity`) is strictly subluminal for `m ≠ 0` (`kgGroupVelocity_abs_lt_one`). This is the free
  field; the interacting/rest-subtracted version is the Compton-clock `kgm*` arc
  (`ComptonClock.HolographicNewtonClockContourGravity`).
* **§C Dimensionless Coulomb orbital quantization.** In atomic (Hartree) units the hydrogenic bound-state
  energies are `E_n = −1/(2n²)` (`coulombEnergy`): all negative (`coulombEnergy_neg`), strictly increasing
  toward the ionization threshold `0` (`coulombEnergy_strictMono`), with ground state `E_1 = −1/2`
  (`coulombEnergy_ground`) and Rydberg–Ritz transition energies `E_n − E_m = ½(1/m² − 1/n²)`
  (`coulombEnergy_rydbergRitz`). The Bohr orbit radius is `r_n = n²` (`bohrOrbitRadius`; the Bohr radius
  `a₀` is `ComptonClock.EntropicMacroscopicLadder`/`Particles.CasimirLengthHierarchy.bohrRadius`). The
  Coulomb virial theorem holds exactly: `E_n = −T_n` (`coulombEnergy_virial_kinetic`) and `V_n = 2E_n`
  (`coulombPotential_eq_two_energy`), with `E_n = T_n + V_n` (`coulombEnergy_eq_kinetic_add_potential`).

## Honest scope

These are the algebraic quantization conditions. The dynamical inputs — that `U(1)` gauge invariance and
single-valued wavefunctions force the phase structure of §A, that the Klein–Gordon operator `□ + m²`
annihilates the plane wave whose temporal factor is §B's mode, and that the Schrödinger–Coulomb
eigenvalue problem yields §C's spectrum — are the standard physics these results encode, taken as the
setup rather than re-derived from an operator eigenvalue problem.
-/

set_option autoImplicit false

open scoped BigOperators

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ElementaryQuantization

/-! ## A. Charge quantization from `U(1)` single-valuedness -/

/-- **The `U(1)` phase** `e^{iqθ}` acquired by a charge-`q` state under a gauge rotation `θ`. -/
noncomputable def chargePhase (q θ : ℝ) : ℂ := Complex.exp ((q * θ : ℝ) * Complex.I)

/-- **Charge quantization.** The `U(1)` phase is single-valued over a full circle — `e^{2πiq} = 1` — if
and only if the charge `q` is an integer. Single-valuedness of the wavefunction quantizes electric
charge. -/
theorem charge_single_valued_iff_int (q : ℝ) :
    Complex.exp ((2 * Real.pi * q : ℝ) * Complex.I) = 1 ↔ ∃ n : ℤ, q = (n : ℝ) := by
  rw [Complex.exp_eq_one_iff]
  refine exists_congr (fun n => ?_)
  constructor
  · intro h
    have e1 : (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
        = ((2 * Real.pi * (n : ℝ) : ℝ) : ℂ) * Complex.I := by push_cast; ring
    rw [e1] at h
    have h2 : (2 * Real.pi * q : ℝ) = 2 * Real.pi * (n : ℝ) := by
      have := mul_right_cancel₀ Complex.I_ne_zero h
      exact_mod_cast this
    have h2pi : (2 * Real.pi) ≠ 0 := by positivity
    exact mul_left_cancel₀ h2pi h2
  · rintro rfl
    push_cast; ring

/-- **Integer charges are closed under addition** — charge conservation is compatible with quantization:
the sum of two quantized charges is quantized. -/
theorem charge_add_quantized {q₁ q₂ : ℝ} (h₁ : ∃ n : ℤ, q₁ = n) (h₂ : ∃ n : ℤ, q₂ = n) :
    ∃ n : ℤ, q₁ + q₂ = (n : ℝ) := by
  obtain ⟨a, rfl⟩ := h₁; obtain ⟨b, rfl⟩ := h₂
  exact ⟨a + b, by push_cast; ring⟩

/-! ## B. Free massive Klein–Gordon evolution -/

/-- **The Klein–Gordon dispersion** `ω(k) = √(k² + m²)` — the positive mass-shell energy of a free mode
of momentum `k` and mass `m`. -/
noncomputable def kgFrequency (k m : ℝ) : ℝ := Real.sqrt (k ^ 2 + m ^ 2)

/-- **The mass shell** `ω² = k² + m²`. -/
theorem kgFrequency_sq (k m : ℝ) : (kgFrequency k m) ^ 2 = k ^ 2 + m ^ 2 := by
  unfold kgFrequency; exact Real.sq_sqrt (by positivity)

/-- **The Lorentz-invariant mass shell** `ω² − k² = m²` (`E² − p² = m²`). -/
theorem kg_massShell (k m : ℝ) : (kgFrequency k m) ^ 2 - k ^ 2 = m ^ 2 := by
  rw [kgFrequency_sq]; ring

/-- **The rest energy is the floor** `|m| ≤ ω(k)`: a massive mode's energy never drops below its rest
mass (equality at `k = 0`). -/
theorem kgFrequency_ge_mass (k m : ℝ) : |m| ≤ kgFrequency k m := by
  unfold kgFrequency
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg k])

/-- **The energy floor is attained at zero momentum** `ω(0) = |m|` — the rest energy. -/
theorem kgFrequency_at_zero (m : ℝ) : kgFrequency 0 m = |m| := by
  unfold kgFrequency; rw [show (0 : ℝ) ^ 2 + m ^ 2 = m ^ 2 by ring, Real.sqrt_sq_eq_abs]

/-- **The free Klein–Gordon temporal mode** `e^{−iω(k)t}` — the time-evolution factor of a mode of
momentum `k`, mass `m`. -/
noncomputable def kgMode (k m t : ℝ) : ℂ := Complex.exp ((-(kgFrequency k m * t) : ℝ) * Complex.I)

/-- **Unitary evolution** `‖e^{−iωt}‖ = 1`: probability is conserved along the free evolution. -/
theorem kgMode_unitary (k m t : ℝ) : ‖kgMode k m t‖ = 1 := by
  unfold kgMode; exact Complex.norm_exp_ofReal_mul_I _

/-- **The evolution starts at the identity** `U(0) = 1`. -/
theorem kgMode_zero (k m : ℝ) : kgMode k m 0 = 1 := by
  unfold kgMode; simp

/-- **The one-parameter group law** `U(t + s) = U(t) U(s)`: the free Klein–Gordon evolution is a
one-parameter unitary group generated by the on-shell energy `ω(k)`. -/
theorem kgMode_add (k m t s : ℝ) : kgMode k m (t + s) = kgMode k m t * kgMode k m s := by
  unfold kgMode
  rw [← Complex.exp_add]
  congr 1
  push_cast; ring

/-- **The group velocity** `v_g = dω/dk = k/ω`. -/
noncomputable def kgGroupVelocity (k m : ℝ) : ℝ := k / kgFrequency k m

/-- **Massive modes are subluminal** `|v_g| < 1` for `m ≠ 0`: the group velocity of a free massive
Klein–Gordon mode is strictly below the speed of light. -/
theorem kgGroupVelocity_abs_lt_one (k m : ℝ) (hm : m ≠ 0) : |kgGroupVelocity k m| < 1 := by
  have hm2 : (0 : ℝ) < m ^ 2 := by rw [pow_two]; exact mul_self_pos.mpr hm
  have hpos : 0 < kgFrequency k m := by
    unfold kgFrequency; rw [Real.sqrt_pos]; nlinarith [sq_nonneg k]
  unfold kgGroupVelocity
  rw [abs_div, abs_of_pos hpos, div_lt_one hpos]
  unfold kgFrequency
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_lt_sqrt (sq_nonneg k) (by linarith)

/-! ## C. Dimensionless Coulomb orbital quantization -/

/-- **The hydrogenic energy levels** `E_n = −1/(2n²)` in atomic (Hartree) units, `n ≥ 1`. -/
noncomputable def coulombEnergy (n : ℕ) : ℝ := -1 / (2 * (n : ℝ) ^ 2)

/-- **The ground state** `E_1 = −1/2` Hartree (`= −1` Rydberg). -/
theorem coulombEnergy_ground : coulombEnergy 1 = -1 / 2 := by norm_num [coulombEnergy]

/-- **The levels are bound states** `E_n < 0` for `n ≥ 1`. -/
theorem coulombEnergy_neg (n : ℕ) (hn : 1 ≤ n) : coulombEnergy n < 0 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  unfold coulombEnergy
  apply div_neg_of_neg_of_pos (by norm_num)
  positivity

/-- **The spectrum is strictly increasing** `E_n < E_{n+1}`: the levels climb monotonically toward the
ionization threshold `0` as the principal quantum number grows. -/
theorem coulombEnergy_strictMono (n : ℕ) (hn : 1 ≤ n) : coulombEnergy n < coulombEnergy (n + 1) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hdiff : coulombEnergy (n + 1) - coulombEnergy n
      = 1 / (2 * (n : ℝ) ^ 2) - 1 / (2 * ((n : ℝ) + 1) ^ 2) := by
    unfold coulombEnergy; push_cast; ring
  have hpos : 0 < 1 / (2 * (n : ℝ) ^ 2) - 1 / (2 * ((n : ℝ) + 1) ^ 2) := by
    have h2n : (0 : ℝ) < 2 * (n : ℝ) ^ 2 := by have := pow_pos hnpos 2; linarith
    rw [sub_pos]
    exact one_div_lt_one_div_of_lt h2n (by nlinarith)
  linarith [hdiff, hpos]

/-- **The Rydberg–Ritz combination principle** `E_n − E_m = ½(1/m² − 1/n²)` — the transition energies
are differences of the quantized levels. -/
theorem coulombEnergy_rydbergRitz (n m : ℕ) :
    coulombEnergy n - coulombEnergy m = 1 / (2 * (m : ℝ) ^ 2) - 1 / (2 * (n : ℝ) ^ 2) := by
  unfold coulombEnergy; ring

/-- **The Bohr orbit radius** `r_n = n²` (in units of the Bohr radius `a₀`). -/
noncomputable def bohrOrbitRadius (n : ℕ) : ℝ := (n : ℝ) ^ 2

/-- **The ground-state orbit is the Bohr radius** `r_1 = 1`. -/
theorem bohrOrbitRadius_ground : bohrOrbitRadius 1 = 1 := by norm_num [bohrOrbitRadius]

/-- **The orbit radius grows with `n`** `r_n < r_{n+1}` (as `n²`). -/
theorem bohrOrbitRadius_strictMono (n : ℕ) (hn : 1 ≤ n) :
    bohrOrbitRadius n < bohrOrbitRadius (n + 1) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  unfold bohrOrbitRadius; push_cast; nlinarith

/-- **The mean kinetic energy** `T_n = 1/(2n²)`. -/
noncomputable def coulombKinetic (n : ℕ) : ℝ := 1 / (2 * (n : ℝ) ^ 2)

/-- **The mean potential energy** `V_n = −1/n²`. -/
noncomputable def coulombPotential (n : ℕ) : ℝ := -1 / (n : ℝ) ^ 2

/-- **The Coulomb virial theorem** `E_n = −T_n`: the total energy is minus the mean kinetic energy. -/
theorem coulombEnergy_virial_kinetic (n : ℕ) : coulombEnergy n = -coulombKinetic n := by
  unfold coulombEnergy coulombKinetic; ring

/-- **The virial ratio** `V_n = 2E_n`: the mean potential energy is twice the total energy. -/
theorem coulombPotential_eq_two_energy (n : ℕ) : coulombPotential n = 2 * coulombEnergy n := by
  unfold coulombPotential coulombEnergy; ring

/-- **Energy decomposition** `E_n = T_n + V_n`. -/
theorem coulombEnergy_eq_kinetic_add_potential (n : ℕ) :
    coulombEnergy n = coulombKinetic n + coulombPotential n := by
  unfold coulombEnergy coulombKinetic coulombPotential; ring

end Physlib.QuantumMechanics.ComplexAction.ElementaryQuantization

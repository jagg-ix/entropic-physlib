/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.GravitationalFieldEquations.MatterFourMomentum

/-!
# The rest frame of the matter, and an inspection of whether the Quantum Inertial Frame supplies it

`GravitationalFieldEquations.MatterFourMomentum` (A1) showed the matter 4-momentum `(E/c, p)` is the Lorentz boost of `(mc, 0)`,
with the bosonic Bogoliubov diagonalized frequency equal to the rest mass `mc`. This file makes the
**rest frame** precise and proves that the bosonic Bogoliubov diagonalization is the passage to it.

It also **inspects** — without assuming correctness — whether the operator-level **Quantum Inertial
Frame** (`FiniteTarget.QuantumInertialFrame`) theorems can be reused for this rest frame, and tests
the question against the Nagao-Nielsen complex oscillator.

## The rest frame is kinematic (`p = 0`)

`IsRestFrame p := (p = 0)` (zero spatial momentum). In the rest frame the energy is the rest energy
`E = mc²` (`rest_frame_energy`), the 4-momentum is `(mc, 0)` (`rest_frame_fourMomentum`), and the
Bogoliubov quadratic Hamiltonian is diagonal `𝔸 = h·1` exactly there
(`bogoliubov_diagonal_iff_rest`). The boost with rapidity `θ` (the Bogoliubov transformation)
generates every momentum from the rest frame (`boost_from_rest`).

## Inspection: the QIF gives the *entropic* frame, not the kinematic rest frame

The Quantum Inertial Frame records `H_R, H_I` with `entropicRate ψ = ⟨H_I⟩/ℏ`, and its
`IsEquilibriumAt` (the "inertial" condition) is `entropicRate = 0`, i.e. `H_I = 0` — **reversibility**
(no entropy production). `QIFLorentzFrameChange` preserves the *entropic rate* under boosts. This is
the **imaginary / entropic axis** (`Im ω`, the dissipative `H_I`), *not* the kinematic rest condition
(`p = 0`, the real momentum).

The two reductions are independent, and the Nagao-Nielsen complex oscillator makes this concrete: the
bosonic quadratic Hamiltonian `𝔸 = [[h, k], [k, h]]` with real `h, k` is **symmetric** (Hermitian as a
complex matrix, so its anti-Hermitian / `H_I` part is `0` — QIF-equilibrium) for **every** `k`
(`quadraticHamiltonian_symm`), whereas the rest frame is the single point `k = 0`. So a reversible
(`H_I = 0`) configuration sits at every momentum (`qif_equilibrium_does_not_imply_rest`): the QIF
equilibrium **cannot single out the rest frame**.

**Conclusion of the inspection.** The QIF's `IsEquilibriumAt` (entropic, `H_I = 0`) is a *different*
reduction from the kinematic rest frame (`p = 0`); they must not be conflated. The QIF frame-change
structure (`QIFLorentzFrameChange`, a unitary coupled to a Lorentz boost) is the right *structure* for
the Bogoliubov boost between frames, but the rest condition is defined kinematically here, not via the
QIF equilibrium. (The two reductions coincide only on the trivial `Im ω = 0 ∧ p = 0` fiber.)

## Main results

* `IsRestFrame`, `rest_frame_energy`, `rest_frame_fourMomentum` — the kinematic rest frame.
* `bogoliubov_diagonal_iff_rest` — the Bogoliubov diagonal frame is the rest frame (`k = 0`).
* `boost_from_rest` — every momentum is the boost of the rest frame.
* `quadraticHamiltonian_symm`, `qif_equilibrium_does_not_imply_rest` — the QIF-equilibrium (entropic)
  is momentum-independent for real data, hence distinct from the rest frame.

## References

* Garcia 2026 (Quantum Inertial Frame; `FiniteTarget.QuantumInertialFrame`, `QIFLorentzFrameChange`).
* P. T. Nam, M. Napiórkowski, J. P. Solovej, J. Funct. Anal. **270** (2016) 4340.
  doi:10.1016/j.jfa.2015.12.007.
* This development: `GravitationalFieldEquations.MatterFourMomentum`, `Bogoliubov.BosonicBogoliubovDiagonalization`,
  `ComplexEinstein.FullEinsteinDispersionConsistency`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

open Matrix
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FullEinsteinDispersionConsistency
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.BosonicBogoliubovDiagonalization
open Physlib.QuantumMechanics.ComplexAction.GravitationalFieldEquations.MatterFourMomentum

namespace Physlib.QuantumMechanics.ComplexAction.Bogoliubov.RestFrame

/-! ## §A — the kinematic rest frame `p = 0` -/

/-- **The rest frame**: the spatial momentum vanishes. -/
def IsRestFrame (p : ℝ) : Prop := p = 0

/-- **In the rest frame the energy is the rest energy** `E = mc²`. -/
theorem rest_frame_energy (m c : ℝ) (h : 0 ≤ m * c ^ 2) :
    einsteinEnergy m c 0 = m * c ^ 2 :=
  einsteinEnergy_rest m c h

/-- **In the rest frame the 4-momentum time component is `mc`** (`E/c = mc`, `p = 0`). -/
theorem rest_frame_fourMomentum (m c : ℝ) (hc : c ≠ 0) (h : 0 ≤ m * c ^ 2) :
    einsteinEnergy m c 0 / c = m * c := by
  rw [rest_frame_energy m c h]
  field_simp

/-! ## §B — the bosonic Bogoliubov diagonalization is the passage to the rest frame -/

/-- **The Bogoliubov diagonal frame is the rest frame**: the quadratic Hamiltonian `𝔸 = [[h,k],[k,h]]`
is diagonal `h·1` iff the pairing `k = 0` — the kinematic rest condition (`p = 0`). -/
theorem bogoliubov_diagonal_iff_rest (h k : ℝ) :
    quadraticHamiltonian h k = h • (1 : Matrix (Fin 2) (Fin 2) ℝ) ↔ k = 0 := by
  constructor
  · intro hd
    have h01 := congrFun (congrFun hd 0) 1
    simpa [quadraticHamiltonian, Matrix.smul_apply, Matrix.one_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons] using h01
  · intro hk
    rw [hk]
    exact bosonicBogoliubov_no_pairing h

/-- **Every momentum is the boost of the rest frame**: there is a rapidity `θ` with `p = mc sinh θ`,
`E/c = mc cosh θ`. The Bogoliubov transformation (boost) generates the moving frames from the rest
frame `(mc, 0)`; the rest frame is the zero-rapidity member. -/
theorem boost_from_rest (m c p : ℝ) (hc : 0 < c) (hm : 0 ≤ m)
    (hsub : |p| < einsteinEnergy m c p / c) :
    ∃ θ : ℝ, p = (m * c) * Real.sinh θ ∧ einsteinEnergy m c p / c = (m * c) * Real.cosh θ :=
  fourMomentum_is_boost_of_rest m c p hc hm hsub

/-- **The rest frame is the zero-rapidity member of the boost orbit**: at `θ = 0`,
`mc sinh 0 = 0` (`p = 0`) and `mc cosh 0 = mc` (`E/c = mc`). -/
theorem rest_frame_zero_rapidity (m c : ℝ) :
    (m * c) * Real.sinh 0 = 0 ∧ (m * c) * Real.cosh 0 = m * c := by
  rw [Real.sinh_zero, Real.cosh_zero]; constructor <;> ring

/-! ## §C — inspection: the QIF equilibrium (entropic) is not the kinematic rest frame -/

/-- **The bosonic quadratic Hamiltonian is symmetric for every `k`** (real symmetric = Hermitian as a
complex matrix, so its anti-Hermitian `H_I` part is `0`). This is the QIF-equilibrium condition, and
it holds for **all** momenta — independently of the rest condition. -/
theorem quadraticHamiltonian_symm (h k : ℝ) :
    (quadraticHamiltonian h k)ᵀ = quadraticHamiltonian h k := by
  unfold quadraticHamiltonian
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.transpose_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]

/-- **The QIF equilibrium does not imply the rest frame.** A real configuration with `k = 1` is
symmetric (Hermitian, `H_I = 0` — QIF-equilibrium / reversible) yet is **not** in the rest frame
(`k ≠ 0`). So the QIF's `IsEquilibriumAt` (entropic, `H_I = 0`) cannot single out the kinematic rest
frame (`p = 0`): they are distinct reductions. The Nagao-Nielsen complex oscillator confirms it —
reversibility (`Im ω = 0`) is momentum-independent. -/
theorem qif_equilibrium_does_not_imply_rest (h : ℝ) :
    (quadraticHamiltonian h 1)ᵀ = quadraticHamiltonian h 1 ∧ ¬ IsRestFrame 1 :=
  ⟨quadraticHamiltonian_symm h 1, by simp [IsRestFrame]⟩

/-! ## §D — the bundled statement -/

/-- **The bosonic Bogoliubov diagonalization is the passage to the rest frame** (kinematic), and the
QIF equilibrium is a distinct (entropic) reduction. For `m ≥ 0`, `c > 0`, sub-luminal `|p| < E/c`:

* the Bogoliubov diagonal frame is the rest frame (`𝔸 = h·1 ⟺ k = 0`);
* in the rest frame `E = mc²`, 4-momentum `(mc, 0)`;
* every momentum is the boost of the rest frame;
* but the QIF-equilibrium (`H_I = 0`, here symmetry) holds at every momentum — it does **not**
  characterize the rest frame. -/
theorem bogoliubov_diagonalization_is_rest_frame (m c p : ℝ) (hc : 0 < c) (hm : 0 ≤ m)
    (hmc : 0 ≤ m * c ^ 2) (hsub : |p| < einsteinEnergy m c p / c) :
    (∀ h k : ℝ, quadraticHamiltonian h k = h • (1 : Matrix (Fin 2) (Fin 2) ℝ) ↔ k = 0)
      ∧ einsteinEnergy m c 0 = m * c ^ 2
      ∧ einsteinEnergy m c 0 / c = m * c
      ∧ (∃ θ : ℝ, p = (m * c) * Real.sinh θ ∧ einsteinEnergy m c p / c = (m * c) * Real.cosh θ)
      ∧ (∀ h : ℝ, (quadraticHamiltonian h 1)ᵀ = quadraticHamiltonian h 1 ∧ ¬ IsRestFrame 1) :=
  ⟨bogoliubov_diagonal_iff_rest, rest_frame_energy m c hmc, rest_frame_fourMomentum m c hc.ne' hmc,
   boost_from_rest m c p hc hm hsub, qif_equilibrium_does_not_imply_rest⟩

end Physlib.QuantumMechanics.ComplexAction.Bogoliubov.RestFrame

end

end

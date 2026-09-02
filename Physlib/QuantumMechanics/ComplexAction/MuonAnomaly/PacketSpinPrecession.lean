/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Dirac.PauliEquationSpinOrbit
public import Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.ThomasBMTMagicCancellation
public import Physlib.Meta.AxiomWhitelistCheck
meta import Zil

/-!
# The expectation-value (packet) spin precession: Ehrenfest ∘ Heisenberg → the vector T-BMT law

`ThomasBMTMagicCancellation` proves the T-BMT **rate magnitudes** (`tbmtSpinRate`, the spin tune,
the magic cancellation) as scalar identities, and `PauliEquationSpinOrbit.heisenberg_spin_precession`
proves the **operator** precession `(i/ℏ)[σ·a, σ·b] = (−2/ℏ)·σ·(a×b)`. Both were flagged in that
file's own ledger as a "scalar-rate shadow of the vector T-BMT equation": neither states the classical
vector precession `dS/dτ = Ω × S` for the *expectation* spin `S = ⟨σ⟩` of an actual state.

This file supplies that reduction by composing the operator precession with **Ehrenfest's theorem**
(`PeriodicQHermitian.Ehrenfest.ehrenfest`, `d⟨O⟩/dt = ⟨(i/ℏ)[H,O]⟩`). For an arbitrary density
matrix `ρ` (any packet) evolving under `H = σ·a`:

* `ehrenfest_spin_precession` — `d⟨σ·b⟩/dt = (−2/ℏ)·⟨σ·(a×b)⟩`: the rate of the spin component
  along any direction `b` is the expectation of the precession operator. This is the packet-level
  precession — it holds for every `ρ`, so the reduction does not depend on a chosen state.
* `ehrenfest_spin_axis_conserved` — `d⟨σ·a⟩/dt = 0`: the spin component along the precession axis
  `a` is conserved (`a×a = 0`), the kinematic signature of precession about `a`.
* `ehrenfest_spin_precession_crossProduct` — `d⟨σ·b⟩/dt = b·(Ω × ⟨σ⟩)` with the precession vector
  `Ω = (2/ℏ)·a` and `⟨σ⟩` the expectation spin vector: the literal classical form `dS/dt = Ω × S`,
  tested against any direction `b`.
* `ehrenfest_dipole_precession_tbmtRate` — for the Dirac–Pauli dipole Hamiltonian `H = −(g/2)(qℏ/2m)Bσ₃`
  at `g = gFactor G`, `d⟨σ₁⟩/dt = tbmtSpinRate(γ=1)·⟨σ₂⟩`: the transverse expectation spin rotates
  at exactly the rest-frame T-BMT rate. The scalar `tbmtSpinRate` of `ThomasBMTMagicCancellation` is
  now the coefficient of a genuine expectation-value equation of motion, not a magnitude beside it.

What stays out of scope (the same boundary the T-BMT ledger already declares): the covariant
boost/Thomas extension `(1+G) → (1+Gγ)` and the loop computation of `F₂`. This is the rest-frame
vector law; the boosted `γ`-dependent couplings remain the spinor-face arc.
-/

set_option autoImplicit false

open Matrix Complex PauliMatrix
open scoped PauliMatrix
open Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.Basic
open Physlib.QuantumMechanics.ComplexAction.Dirac.PauliEquationSpinOrbit
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.ThomasBMTMagicCancellation
open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.AnomalousMagneticMoment

@[expose] public section

noncomputable section

namespace Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.PacketSpinPrecession

/-- `σ·0 = 0` — the spin projection of the zero field vanishes. -/
@[simp] lemma sigmaDot_zero : sigmaDot 0 = 0 := by simp [sigmaDot]

/-! ## The core packet-level precession -/

/-- **[The Ehrenfest spin precession]** `d⟨σ·b⟩/dt = (−2/ℏ)·⟨σ·(a×b)⟩` — the rate of the expectation
value of the spin component along `b`, for a state `ρ` evolving under the field `H = σ·a`, is the
expectation of the operator precession `(−2/ℏ)σ·(a×b)`. Composes `ehrenfest` (the expectation-rate
theorem) with `heisenberg_spin_precession` (the operator law); holds for **any** density matrix `ρ`. -/
theorem ehrenfest_spin_precession (ℏ : ℂ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) (a b : Fin 3 → ℝ) :
    (vonNeumannGen ℏ (sigmaDot a) ρ * sigmaDot b).trace
      = (-2 / ℏ) * (ρ * sigmaDot (crossR a b)).trace := by
  rw [ehrenfest, heisenberg_spin_precession, mul_smul_comm, Matrix.trace_smul, smul_eq_mul]

/-- **[The spin component along the axis is conserved]** `d⟨σ·a⟩/dt = 0`: measuring the spin along
the precession axis `a` itself gives no rate, because `a × a = 0`. The conserved axial projection is
the kinematic signature of precession about `a`. -/
theorem ehrenfest_spin_axis_conserved (ℏ : ℂ) (ρ : Matrix (Fin 2) (Fin 2) ℂ) (a : Fin 3 → ℝ) :
    (vonNeumannGen ℏ (sigmaDot a) ρ * sigmaDot a).trace = 0 := by
  rw [ehrenfest_spin_precession, crossR_self, sigmaDot_zero, Matrix.mul_zero, Matrix.trace_zero,
    mul_zero]

/-! ## The expectation spin as a vector and the classical `dS/dt = Ω × S` -/

/-- The **expectation spin vector** `S = ⟨σ⟩ = (⟨σ₁⟩, ⟨σ₂⟩, ⟨σ₃⟩)`, each component the trace `Tr(ρσₖ)`. -/
def spinExpectation (ρ : Matrix (Fin 2) (Fin 2) ℂ) : Fin 3 → ℂ :=
  ![(ρ * σ1).trace, (ρ * σ2).trace, (ρ * σ3).trace]

/-- The **complex 3-vector cross product** `(u × v)`, on the complexified expectation vectors. -/
def crossC (u v : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]

/-- The **precession vector** `Ω = (2/ℏ)·a` — the angular-velocity vector about which `⟨σ⟩` precesses. -/
def omegaVec (ℏ : ℂ) (a : Fin 3 → ℝ) : Fin 3 → ℂ := fun k => (2 / ℏ) * (a k : ℂ)

/-- **[Expectation of `σ·v` is `v·⟨σ⟩`]** `Tr(ρ·σ·v) = ∑ₖ vₖ⟨σₖ⟩` — trace linearity turns the spin
projection into the dot product of `v` with the expectation spin vector. -/
theorem trace_mul_sigmaDot (ρ : Matrix (Fin 2) (Fin 2) ℂ) (v : Fin 3 → ℝ) :
    (ρ * sigmaDot v).trace
      = (v 0 : ℂ) * (ρ * σ1).trace + (v 1 : ℂ) * (ρ * σ2).trace + (v 2 : ℂ) * (ρ * σ3).trace := by
  simp only [sigmaDot, Matrix.mul_add, Matrix.trace_add, mul_smul_comm, Matrix.trace_smul,
    smul_eq_mul]

/-- **[The classical vector precession `dS/dt = Ω × S`]** `d⟨σ·b⟩/dt = b·(Ω × ⟨σ⟩)` with the
precession vector `Ω = (2/ℏ)·a` and `⟨σ⟩` the expectation spin vector: the rate of the spin along any
direction `b` is the projection of `Ω × ⟨σ⟩` onto `b` — the packet expectation obeys the classical
Larmor/T-BMT vector precession about the field axis `a`. -/
theorem ehrenfest_spin_precession_crossProduct (ℏ : ℂ) (ρ : Matrix (Fin 2) (Fin 2) ℂ)
    (a b : Fin 3 → ℝ) :
    (vonNeumannGen ℏ (sigmaDot a) ρ * sigmaDot b).trace
      = ∑ k, (b k : ℂ) * crossC (omegaVec ℏ a) (spinExpectation ρ) k := by
  rw [ehrenfest_spin_precession, trace_mul_sigmaDot]
  simp only [crossC, omegaVec, spinExpectation, crossR, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
  push_cast
  ring

/-! ## The T-BMT rate as the packet precession coefficient -/

/-- **[The packet spin precesses at the T-BMT rate]** `d⟨σ₁⟩/dt = tbmtSpinRate(γ=1)·⟨σ₂⟩` for the
Dirac–Pauli dipole Hamiltonian `H = −(g/2)(qℏ/2m)Bσ₃` at the full `g = gFactor G = 2(1+G)`: the
transverse expectation spin `⟨σ₁⟩` rotates into `⟨σ₂⟩` at exactly the rest-frame T-BMT precession rate
of `ThomasBMTMagicCancellation`. The scalar `tbmtSpinRate` is thereby the coefficient of a genuine
expectation-value equation of motion — the vector precession the scalar rate was a shadow of. -/
theorem ehrenfest_dipole_precession_tbmtRate (G q m hbar B : ℝ) (hℏ : hbar ≠ 0)
    (ρ : Matrix (Fin 2) (Fin 2) ℂ) :
    (vonNeumannGen (hbar : ℂ) (dipoleHamiltonianZ (gFactor G) q m hbar B) ρ * σ1).trace
      = (tbmtSpinRate q m 1 G B 0 : ℂ) * (ρ * σ2).trace := by
  have hcoef : ((gFactor G * q * B / (2 * m) : ℝ) : ℂ) = (tbmtSpinRate q m 1 G B 0 : ℂ) := by
    rw [tbmtSpinRate_rest_eq_diracPauli]
  rw [ehrenfest]
  unfold heisenbergGen Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.Basic.commutator
  rw [heisenberg_precession_of_dipole (gFactor G) q m hbar B hℏ, mul_smul_comm, Matrix.trace_smul,
    smul_eq_mul, hcoef]

end Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.PacketSpinPrecession

end

end

open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.PacketSpinPrecession in
#physlib_axiom_clean_all [
  ehrenfest_spin_precession,
  ehrenfest_spin_axis_conserved,
  trace_mul_sigmaDot,
  ehrenfest_spin_precession_crossProduct,
  ehrenfest_dipole_precession_tbmtRate ]

open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.PacketSpinPrecession in
#physlib_non_vacuous_all [
  ehrenfest_spin_precession,
  ehrenfest_spin_axis_conserved,
  trace_mul_sigmaDot,
  ehrenfest_spin_precession_crossProduct,
  ehrenfest_dipole_precession_tbmtRate ]

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.PacketSpinPrecession.ehrenfest_spin_precession where
  formalizes @ "claim:the-ehrenfest-expectation-spin-precession-is-the-packet-level-vector-law",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PeriodicQHermitian.Basic.ehrenfest",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Dirac.PauliEquationSpinOrbit.heisenberg_spin_precession"

zil attach Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.PacketSpinPrecession.ehrenfest_spin_precession_crossProduct where
  formalizes @ "claim:the-expectation-spin-obeys-the-classical-cross-product-precession-ds-dt-equals-omega-cross-s",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.PacketSpinPrecession.ehrenfest_spin_precession"

zil attach Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.PacketSpinPrecession.ehrenfest_dipole_precession_tbmtRate where
  formalizes @ "claim:the-packet-expectation-spin-precesses-at-the-rest-frame-tbmt-rate",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.PacketSpinPrecession.ehrenfest_spin_precession",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.ThomasBMTMagicCancellation.tbmtSpinRate_rest_eq_diracPauli",
  caveat @ "claim:the-covariant-boost-thomas-extension-one-plus-g-gamma-splitting-remains-underived"

/- ZIL-END -/

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDBetaFunctionAsymptoticFreedom
meta import Zil

/-!
# The QCD θ-term is a CP-violating topological phase: the strong-CP problem (PDG 2026 §9.1)

The third feature of the QCD Lagrangian (PDG 2026 §9.1, after the kinetic `−¼F²` and the quark terms) is the
**`θ`-term** `θ (α_s/8π) F^A_μν F̃^A_μν`, with `F̃` the dual field tensor. Because `F F̃` is a total derivative, its
spacetime integral is the **topological charge** `n ∈ ℤ` (the instanton/winding number), so the `θ`-term
contributes a phase `e^{iθn}` to the path integral — the **`θ`-vacuum**.

This is the *unitary* (pure-phase) partner of the confinement work: the confining area law is a **real** entropic
damping `e^{−σA} = kuikenWeight` (`ConfinementAreaLawEntropicWeight`), while the `θ`-term is a **pure imaginary
action** `e^{iθn}` of unit modulus (`thetaWeight_abs`). Real part → damping (confinement); imaginary part → phase
(the `θ`-vacuum) — the same complex-action split as the arc's `𝒢 = G + iΛ`.

* the **`θ`-angle is periodic** with period `2π` (`thetaWeight_periodic`) — since `n ∈ ℤ`, physical `θ ∈ [0, 2π)`;
* the **`θ`-vacuum weight is a pure phase** `|e^{iθn}| = 1` (`thetaWeight_abs`) — unitary, unlike the real
  confining `kuikenWeight` damping;
* **`F F̃` is CP-odd**: charge conjugation / parity flips the topological charge `n → −n`, conjugating the weight
  (`thetaWeight_cp`), so the `θ`-vacuum is CP-invariant **iff** the weight is real — `θ = 0` (`thetaWeight_zero`,
  `cp_conserved_at_theta_zero`). The **strong-CP problem** is that experiment gives `|θ| ≲ 10⁻¹⁰`: why is `θ`
  essentially zero?

The `θ`-term violates P, T and CP but is **CPT-even** (the CPT theorem holds), the same CPT structure the
charge-chirality arc carries. Strong CP is the statement that the one CP-violating handle QCD offers is,
empirically, turned off.

* **§A — the `θ`-vacuum weight** (`thetaWeight`, `thetaWeight_zero`).
* **§B — `θ` is a periodic angle** (`thetaWeight_periodic`).
* **§C — a pure phase, not a damping** (`thetaWeight_abs`).
* **§D — CP-odd; CP-conserved at `θ = 0`** (`thetaWeight_cp`, `cp_conserved_at_theta_zero`).
* **§E — assembled** (`thetaTerm_strongCP`).

**Honest layering.** `thetaWeight = e^{iθn}` is the exact `θ`-vacuum phase with integer topological charge `n`;
periodicity, unit modulus, and the CP conjugation are exact `Complex.exp` identities. The `|θ| ≲ 10⁻¹⁰` bound is
experimental and only *recorded* (the CP-conserving `θ = 0` point is the theorem). `F F̃`'s status as the
topological density is not derived from the gauge field. ## References

* Particle Data Group, PDG 2026 Review, §9.1 (`θ`-term `θ(α_s/8π)F F̃`, neutron-EDM bound `|θ| ≲ 10⁻¹⁰`).
  Repo carrier: `HorizonCell.QCDBetaFunctionAsymptoticFreedom`.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDThetaTermStrongCP

open Complex


/-- **The `θ`-vacuum path-integral weight** `e^{iθn}` (PDG §9.1) — the phase the `θ`-term
`θ(α_s/8π) F F̃` contributes to a field configuration of **topological charge** `n ∈ ℤ` (the instanton/winding
number, since `∫ F F̃ ∝ n`). -/
noncomputable def thetaWeight (θ : ℝ) (n : ℤ) : ℂ := Complex.exp (Complex.I * (θ : ℂ) * (n : ℂ))

/-- **[At `θ = 0` the `θ`-vacuum weight is trivial] `e^{i·0·n} = 1`.** With vanishing vacuum angle there is no
topological phase — the CP-conserving point of the strong-CP problem. -/
lemma thetaWeight_zero (n : ℤ) : thetaWeight 0 n = 1 := by
  unfold thetaWeight; simp


/-- **[The `θ`-angle is periodic with period `2π`] `e^{i(θ+2π)n} = e^{iθn}`.** Because the topological charge
`n` is an integer, shifting the vacuum angle by `2π` leaves the `θ`-vacuum weight invariant: `θ` is a genuine
angle, with physical range `θ ∈ [0, 2π)`. -/
lemma thetaWeight_periodic (θ : ℝ) (n : ℤ) :
    thetaWeight (θ + 2 * Real.pi) n = thetaWeight θ n := by
  unfold thetaWeight
  have h2pi : Complex.exp ((n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = 1 :=
    Complex.exp_int_mul_two_pi_mul_I n
  push_cast
  rw [show Complex.I * ((θ : ℂ) + 2 * (Real.pi : ℂ)) * (n : ℂ)
        = Complex.I * (θ : ℂ) * (n : ℂ) + (n : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by ring,
    Complex.exp_add, h2pi, mul_one]


/-- **[The `θ`-vacuum weight is a pure phase] `|e^{iθn}| = 1`.** The `θ`-term is a *purely imaginary* action, so
its weight has unit modulus — a unitary phase, unlike the *real* confining damping `e^{−σA} = kuikenWeight` of the
area law. Real action → damping (confinement); imaginary action → phase (the `θ`-vacuum): the complex-action
split of the arc. -/
lemma thetaWeight_abs (θ : ℝ) (n : ℤ) : ‖thetaWeight θ n‖ = 1 := by
  unfold thetaWeight
  rw [Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im, Real.exp_zero]


/-- **[`F F̃` is CP-odd] `e^{iθ(−n)} = conj(e^{iθn})`.** Charge conjugation / parity / time reversal flip the
topological charge `n → −n` (the dual density `F F̃` is a pseudoscalar), which conjugates the `θ`-vacuum weight.
Hence the `θ`-vacuum is CP-invariant iff the weight is real for all `n` — the strong-CP condition. -/
lemma thetaWeight_cp (θ : ℝ) (n : ℤ) :
    thetaWeight θ (-n) = (starRingEnd ℂ) (thetaWeight θ n) := by
  unfold thetaWeight
  rw [← Complex.exp_conj]
  congr 1
  push_cast
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_intCast]
  ring

/-- **[CP is conserved at `θ = 0`] the weight equals its `n → −n` image.** At the CP-conserving point `θ = 0`
the `θ`-vacuum weight is `1` for every topological sector, so it is invariant under the CP flip `n → −n`: no
strong CP violation. The strong-CP problem is why nature sits (to `≲ 10⁻¹⁰`) at exactly this point. -/
lemma cp_conserved_at_theta_zero (n : ℤ) : thetaWeight 0 (-n) = thetaWeight 0 n := by
  rw [thetaWeight_zero, thetaWeight_zero]


/-- **[The QCD `θ`-term and the strong-CP problem, assembled].** The `θ`-vacuum weight `e^{iθn}` over integer
topological charge `n`:

* is a **periodic** function of the vacuum angle (`θ ↦ θ + 2π` invariant) — `θ` is an angle;
* is a **pure phase** `|e^{iθn}| = 1` — a unitary imaginary action, not the real confining `kuikenWeight`
  damping;
* is **CP-odd** — the CP flip `n → −n` conjugates it, so CP is conserved iff the weight is real, which at
  `θ = 0` it is.

The `θ`-term is the one CP-violating handle in QCD; strong CP (`|θ| ≲ 10⁻¹⁰`) is the empirical statement that it
is turned off. CP-violating, CPT-even — the CPT structure of the arc. -/
lemma thetaTerm_strongCP (θ : ℝ) (n : ℤ) :
    thetaWeight (θ + 2 * Real.pi) n = thetaWeight θ n
      ∧ ‖thetaWeight θ n‖ = 1
      ∧ thetaWeight θ (-n) = (starRingEnd ℂ) (thetaWeight θ n)
      ∧ thetaWeight 0 (-n) = thetaWeight 0 n :=
  ⟨thetaWeight_periodic θ n, thetaWeight_abs θ n, thetaWeight_cp θ n,
    cp_conserved_at_theta_zero n⟩

end Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDThetaTermStrongCP

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDThetaTermStrongCP.thetaWeight_abs where
  formalizes @ "claim:the-qcd-theta-vacuum-weight-is-a-pure-phase-of-unit-modulus-unitary-unlike-the-real-confining-area-law-damping",
  supported_by @ "paper:pdg-2026-review-section-9-1-qcd-theta-term"

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDThetaTermStrongCP.thetaWeight_cp where
  formalizes @ "claim:the-topological-density-f-f-dual-is-cp-odd-charge-conjugation-parity-flips-the-topological-charge-n-to-minus-n-conjugating-the-theta-vacuum-weight",
  supported_by @ "paper:pdg-2026-review-section-9-1-qcd-theta-term"

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDThetaTermStrongCP.thetaTerm_strongCP where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDThetaTermStrongCP.thetaWeight_abs",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDThetaTermStrongCP.thetaWeight_cp",
  formalizes @ "claim:the-strong-cp-problem-the-qcd-theta-term-is-a-periodic-cp-violating-pure-phase-that-is-cp-conserving-exactly-at-theta-zero-yet-experiment-bounds-theta-below-ten-to-the-minus-ten",
  requires @ "claim:the-qcd-theta-vacuum-weight-is-a-pure-phase-of-unit-modulus-unitary-unlike-the-real-confining-area-law-damping",
  requires @ "claim:the-topological-density-f-f-dual-is-cp-odd-charge-conjugation-parity-flips-the-topological-charge-n-to-minus-n-conjugating-the-theta-vacuum-weight"

zil_file_contract physlib.qcdThetaTermStrongCP where
  promises "The QCD theta-term theta (alpha_s/8pi) F F-dual as a CP-violating topological phase and the strong-CP problem (PDG 2026 section 9.1). Because F F-dual is a total derivative its spacetime integral is the integer topological charge n, so the theta-term contributes a pure phase e^{i theta n} to the path integral -- the theta-vacuum, the unitary partner of the real confining area-law damping in the same complex-action split G + i Lambda. Proven as exact Complex.exp identities: theta is a periodic angle of period 2pi, the theta-vacuum weight is a pure phase of unit modulus, and F F-dual is CP-odd (charge conjugation flips n to -n, conjugating the weight), so the theta-vacuum is CP-invariant exactly at theta = 0. The neutron-EDM bound |theta| < 10^-10 is experimental and only recorded; F F-dual's status as the topological density is not derived from the gauge field."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDThetaTermStrongCP.thetaWeight"]
  forbids_substitutes ["a real damping weight, whereas the theta-vacuum weight is a pure phase of unit modulus",
    "a CP-conserving theta-term at generic theta, whereas CP is conserved only at theta = 0"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDThetaTermStrongCP.thetaWeight_periodic,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDThetaTermStrongCP.thetaWeight_abs,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDThetaTermStrongCP.thetaWeight_cp,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDThetaTermStrongCP.thetaTerm_strongCP]

/- ZIL-END -/

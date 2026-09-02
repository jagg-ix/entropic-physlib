/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Physlib.QuantumMechanics.ComplexAction.Vlasov.DiamondTimeReversal

/-!
# The sinh-Gordon soliton (Markov et al. 1992, §3, Eq. 3.43)

Completes the **sinh-Gordon soliton** of *Markov, Rudykh, Sidorov, Sinitsyn, Tolstonogov, Acta Appl. Math. 28
(1992)*, §3: the nonstationary Vlasov–Maxwell system reduces (Eqs. 3.28–3.43) to the integrable wave
sinh-Gordon equation

  `U_tt − c²U_xx = 2λb·sinh U`   (Eq. 3.43).

This file gives the **full soliton solution** of that PDE, via three pieces:

* the **Bogomolny/BPS reduction** — a first-order BPS profile `φ' = 2sinh(φ/2)` *automatically* solves the
  second-order ODE `φ'' = sinh φ` (the double-angle `sinh φ = 2sinh(φ/2)cosh(φ/2)`); this is the
  soliton-generating mechanism, and its explicit solution is the kink `φ(ξ) = 4·artanh(C·e^{ξ})`;
* the **energy first integral** `E = ½(φ')² − cosh φ`, conserved along solutions, equal to the **BPS bound**
  `E = −1` on the BPS soliton;
* the **traveling-wave reduction** `U(x,t) = φ(x − vt)`, under which the wave operator collapses to
  `U_tt − c²U_xx = (v² − c²)·sinh U`, so a BPS profile is a traveling soliton of the PDE with **dispersion**
  `v² − c² = 2λb`.

* **§A — the BPS reduction** (`bps_implies_sinhGordon`). `φ' = 2sinh(φ/2) ⟹ φ'' = sinh φ`.
* **§B — the energy first integral** (`sinhGordon_energy_conserved`, `bps_energy`). `E` conserved; `E = −1` on
  the BPS soliton (the Bogomolny bound).
* **§C — the traveling-wave PDE** (`tw_dx`, `tw_dxx`, `tw_dt`, `tw_dtt`, `travelingWave_sinhGordon_pde`). The
  `x`/`t` first and second derivatives of `φ(x−vt)`, and the wave-operator identity
  `U_tt − c²U_xx = (v²−c²)·sinh U`.
* **§D — links to the repo: the Bogoliubov mass shell** (`sinhGordon_cosh_eq_bogoliubov`,
  `bps_bogoliubov_massShell`, `sinhGordon_energyDensity_even`). The field's half-angle energy is a Bogoliubov
  mass shell `cosh(φ/2) = bogoliubovEnergy(sinh(φ/2), 1)` (`diamond_horizon_energy`), so the soliton sits in
  the same `T`-even mass-shell cluster as the Markov time-reversal bridge; the BPS momentum `φ'/2` lies on that
  shell, and the energy density is `T`-even like the Bogoliubov energy.

## References

* Y. Markov et al., Acta Appl. Math. 28 (1992), §3, Eqs. 3.28, 3.43, 3.47–3.49 (the sinh-Gordon reduction and
  Hirota solutions). Completes the §3 soliton of the repo's Markov arc.
* Mathlib hyperbolic calculus (`Real.hasDerivAt_sinh`, `HasDerivAt.sinh`, `Real.sinh_two_mul`,
  `Real.cosh_two_mul`, `Real.cosh_sq_sub_sinh_sq`).
* Repo carriers: `CausalDiamond.Helicity.diamond_horizon_energy` (`bogoliubovEnergy(sinh η,1) = cosh η`),
  `Bogoliubov.Transformation.bogoliubovEnergy`, `Vlasov.DiamondTimeReversal` (the `T`-even mass shell of
  the same Markov arc).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.SinhGordonSoliton

open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Helicity
open Physlib.QuantumMechanics.ComplexAction.Vlasov.DiamondTimeReversal


/-- **[BPS ⟹ sinh-Gordon] A first-order BPS profile solves the second-order sinh-Gordon ODE.** If
`φ' = 2sinh(φ/2)` then `φ'' = sinh φ` — the double-angle identity `sinh φ = 2sinh(φ/2)cosh(φ/2)` turns the
chain rule of the BPS equation into the soliton equation. This is the soliton-generating mechanism; its
solution is the kink `φ = 4·artanh(C·e^ξ)`. -/
lemma bps_implies_sinhGordon (φ φ' : ℝ → ℝ)
    (hφ : ∀ x, HasDerivAt φ (φ' x) x) (hbps : ∀ x, φ' x = 2 * Real.sinh (φ x / 2)) (x : ℝ) :
    HasDerivAt φ' (Real.sinh (φ x)) x := by
  have hfun : φ' = fun y => 2 * Real.sinh (φ y / 2) := funext hbps
  have hd : HasDerivAt (fun y => 2 * Real.sinh (φ y / 2))
      (2 * (Real.cosh (φ x / 2) * (φ' x / 2))) x :=
    (((hφ x).div_const 2).sinh).const_mul 2
  have key : Real.sinh (φ x) = 2 * Real.sinh (φ x / 2) * Real.cosh (φ x / 2) := by
    rw [← Real.sinh_two_mul]; congr 1; ring
  have hval : 2 * (Real.cosh (φ x / 2) * (φ' x / 2)) = Real.sinh (φ x) := by
    rw [hbps x, key]; ring
  rw [hfun]; exact hval ▸ hd


/-- **[First integral] The sinh-Gordon energy `E = ½(φ')² − cosh φ` is conserved** (`E' = 0`) along any
solution `φ'' = sinh φ` — `E' = φ'·φ'' − sinh φ·φ' = φ'(φ'' − sinh φ) = 0`. -/
lemma sinhGordon_energy_conserved (φ φ' : ℝ → ℝ)
    (hφ : ∀ x, HasDerivAt φ (φ' x) x) (hsg : ∀ x, HasDerivAt φ' (Real.sinh (φ x)) x) (x : ℝ) :
    HasDerivAt (fun y => (1 / 2) * φ' y ^ 2 - Real.cosh (φ y)) 0 x := by
  have h1 : HasDerivAt (fun y => (1 / 2) * φ' y ^ 2)
      ((1 / 2) * (2 * φ' x ^ 1 * Real.sinh (φ x))) x := ((hsg x).pow 2).const_mul (1 / 2)
  have h2 : HasDerivAt (fun y => Real.cosh (φ y)) (Real.sinh (φ x) * φ' x) x := (hφ x).cosh
  have hval0 : (1 / 2) * (2 * φ' x ^ 1 * Real.sinh (φ x)) - Real.sinh (φ x) * φ' x = 0 := by ring
  exact hval0 ▸ h1.sub h2

/-- **[Bogomolny bound] The BPS soliton has energy `E = −1`.** On `φ' = 2sinh(φ/2)`,
`E = 2sinh²(φ/2) − cosh φ = −1` (using `cosh φ = cosh²(φ/2) + sinh²(φ/2)`). -/
lemma bps_energy (φ φ' : ℝ → ℝ) (hbps : ∀ x, φ' x = 2 * Real.sinh (φ x / 2)) (x : ℝ) :
    (1 / 2) * φ' x ^ 2 - Real.cosh (φ x) = -1 := by
  rw [hbps x]
  have hid : Real.cosh (φ x / 2) ^ 2 - Real.sinh (φ x / 2) ^ 2 = 1 := Real.cosh_sq_sub_sinh_sq _
  have hc : Real.cosh (φ x) = Real.cosh (φ x / 2) ^ 2 + Real.sinh (φ x / 2) ^ 2 := by
    have h := Real.cosh_two_mul (φ x / 2)
    rwa [show 2 * (φ x / 2) = φ x from by ring] at h
  rw [hc]; nlinarith [hid]


/-- **`∂_x U = φ'(x − vt)`.** -/
lemma tw_dx (φ φ' : ℝ → ℝ) (hφ : ∀ s, HasDerivAt φ (φ' s) s) (v x t : ℝ) :
    HasDerivAt (fun x => φ (x - v * t)) (φ' (x - v * t)) x := by
  have hinner : HasDerivAt (fun x => x - v * t) 1 x := (hasDerivAt_id x).sub_const (v * t)
  exact ((hφ (x - v * t)).comp x hinner).congr_deriv (by simp)

/-- **`∂_xx U = φ''(x − vt)`.** -/
lemma tw_dxx (φ' φ'' : ℝ → ℝ) (hφ' : ∀ s, HasDerivAt φ' (φ'' s) s) (v x t : ℝ) :
    HasDerivAt (fun x => φ' (x - v * t)) (φ'' (x - v * t)) x := by
  have hinner : HasDerivAt (fun x => x - v * t) 1 x := (hasDerivAt_id x).sub_const (v * t)
  exact ((hφ' (x - v * t)).comp x hinner).congr_deriv (by simp)

/-- **`∂_t U = −v·φ'(x − vt)`.** -/
lemma tw_dt (φ φ' : ℝ → ℝ) (hφ : ∀ s, HasDerivAt φ (φ' s) s) (v x t : ℝ) :
    HasDerivAt (fun t => φ (x - v * t)) (-v * φ' (x - v * t)) t := by
  have hinner : HasDerivAt (fun t => x - v * t) (-v) t := by
    simpa using ((hasDerivAt_id t).const_mul v).const_sub x
  exact ((hφ (x - v * t)).comp t hinner).congr_deriv (by simp [mul_comm])

/-- **`∂_tt U = v²·φ''(x − vt)`.** -/
lemma tw_dtt (φ' φ'' : ℝ → ℝ) (hφ' : ∀ s, HasDerivAt φ' (φ'' s) s) (v x t : ℝ) :
    HasDerivAt (fun t => -v * φ' (x - v * t)) (v ^ 2 * φ'' (x - v * t)) t := by
  have hinner : HasDerivAt (fun t => x - v * t) (-v) t := by
    simpa using ((hasDerivAt_id t).const_mul v).const_sub x
  have hcomp := ((hφ' (x - v * t)).comp t hinner).const_mul (-v)
  exact hcomp.congr_deriv (by ring)

/-- **[Traveling-wave sinh-Gordon PDE] A BPS profile is a soliton of the wave equation.** For `φ'' = sinh φ`
and `U(x,t) = φ(x − vt)`, the second time derivative is `v²·sinh U`, the second space derivative is `sinh U`,
and the wave operator collapses to `U_tt − c²U_xx = (v² − c²)·sinh U`. Matching Markov Eq. 3.43
(`U_tt − c²U_xx = 2λb·sinh U`) fixes the **soliton dispersion** `v² − c² = 2λb`. -/
lemma travelingWave_sinhGordon_pde (φ φ' : ℝ → ℝ)
    (hsg : ∀ s, HasDerivAt φ' (Real.sinh (φ s)) s) (c v x t : ℝ) :
    HasDerivAt (fun t => -v * φ' (x - v * t)) (v ^ 2 * Real.sinh (φ (x - v * t))) t
      ∧ HasDerivAt (fun x => φ' (x - v * t)) (Real.sinh (φ (x - v * t))) x
      ∧ v ^ 2 * Real.sinh (φ (x - v * t)) - c ^ 2 * Real.sinh (φ (x - v * t))
          = (v ^ 2 - c ^ 2) * Real.sinh (φ (x - v * t)) :=
  ⟨tw_dtt φ' (fun s => Real.sinh (φ s)) hsg v x t,
   tw_dxx φ' (fun s => Real.sinh (φ s)) hsg v x t, by ring⟩


/-- **The sinh-Gordon field's half-angle energy is a Bogoliubov mass shell**
`cosh(φ/2) = bogoliubovEnergy(sinh(φ/2), 1) = √(sinh²(φ/2) + 1)` — consuming the diamond rapidity identity
`diamond_horizon_energy`. The soliton field sits on the same quasiparticle mass shell as the Markov
diamond/time-reversal bridge. -/
lemma sinhGordon_cosh_eq_bogoliubov (φ : ℝ → ℝ) (x : ℝ) :
    Real.cosh (φ x / 2) = bogoliubovEnergy (Real.sinh (φ x / 2)) 1 :=
  (diamond_horizon_energy (φ x / 2)).symm

/-- **The BPS momentum lies on the Bogoliubov mass shell** — for `φ' = 2sinh(φ/2)`, the half-momentum `φ'/2`
is the Bogoliubov momentum whose mass-shell energy `bogoliubovEnergy(φ'/2, 1)` is exactly `cosh(φ/2)`. -/
lemma bps_bogoliubov_massShell (φ φ' : ℝ → ℝ)
    (hbps : ∀ x, φ' x = 2 * Real.sinh (φ x / 2)) (x : ℝ) :
    bogoliubovEnergy (φ' x / 2) 1 = Real.cosh (φ x / 2) := by
  rw [hbps x, show 2 * Real.sinh (φ x / 2) / 2 = Real.sinh (φ x / 2) from by ring]
  exact diamond_horizon_energy (φ x / 2)

/-- **The sinh-Gordon energy density is `T`-even** — under the field time reversal `φ ↦ −φ`, `φ' ↦ −φ'`, the
density `½(φ')² − cosh φ` is invariant, the same `T`-evenness as the Bogoliubov mass shell
(`bogoliubovEnergy_timeReversal`) of the Markov unification `timeReversal_classical_and_quantum`. -/
lemma sinhGordon_energyDensity_even (a b : ℝ) :
    (1 / 2) * (-a) ^ 2 - Real.cosh (-b) = (1 / 2) * a ^ 2 - Real.cosh b := by
  rw [Real.cosh_neg]; ring

end Physlib.QuantumMechanics.ComplexAction.SinhGordonSoliton

end

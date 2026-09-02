/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Particles.QuantumDrudeOscillatorInvariants
public import Physlib.QuantumMechanics.ComplexAction.Particles.DispersiveForceEntanglement
public import Physlib.QuantumMechanics.ComplexAction.VanDerWaalsPolarizabilityScaling
public import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Lennard-Jones + Axilrod-Teller-Muto and their one microscopic origin: the QDO dispersion

The dispersion-force sector in three namespaces (each formerly its own module):

* **Part I — `LennardJonesAxilrodTeller`.** The interaction potentials of Robles-Navarro, Cooper,
  Buchheit, Busse, Burrows, Smits & Schwerdtfeger (arXiv:2504.07338, 2025): the general `(n,m)`
  Lennard-Jones potential with the exact well depth `E_LJ(rₑ) = −ε` (`lj_at_re`), the
  Axilrod-Teller-Muto angular factor `1 + 3c₁c₂c₃` with its geometry-dependent sign
  (`atm_equilateral` `= 11/8 > 0` repulsive vs `atm_linear` `= −2 < 0` attractive — why repulsive ATM
  destabilizes fcc), the identification `λ = C₉ = 3/16 α₁³ℏω` (`atmEnergy_coupling_eq_C9`), and the
  Bain-path `c/a` endpoints `bcc = 1`, `fcc = √2` (`fccRatio_sq`).
* **Part II — `QuantumDrudeOscillatorVanDerWaals`.** The QDO invariants applied to the concrete
  polarizability `α₁ = q²/(μω²)` that drives the vdW radius law: `polarizability_invariant_qdo`,
  `dispersion_invariant_qdo`, the `C₆`↔`dispersionEnergy` identification (`dispersionEnergy_eq_C6`),
  the `R_vdW ∝ α^{1/7}` law with the QDO polarizability (`qdo_vdw_radius_seventh`), and the octupole
  `α₃^{1/14}` exponent.
* **Part III — `LennardJonesDispersion`.** The linkage: the LJ potential splits as repulsion minus
  attraction (`ljPotential_split`), the `m = 6` tail has the `−C₆/R⁶` dispersion form
  (`lj_tail_dispersion_form`, `= dispersionEnergy` via `lj_tail_eq_vdw_dispersionEnergy`, `= −C₆/r⁶`
  of the QDO when the coefficients agree, `lj_tail_is_qdo_C6`), and the two- and three-body lattice
  couplings are one QDO's `C₆, C₉` related by its three-body invariant `α₁·C₆ = 4·C₉`
  (`lattice_couplings_qdo_related`) with the even/odd dispersion sign structure
  (`two_body_binds_three_body_signed`).

**Honest layering.** The well depth, ATM angular values, Bain endpoints, invariant applications, and
all tail identities are exact `ring`/`field_simp` equalities; `λ = C₉` and the `C₆` identifications
tie the lattice phenomenology to the microscopic QDO. The lattice sums (Epstein-zeta continuations)
and the numerical Bain-path stability analysis of the paper are not formalized here.

## References

* Robles-Navarro et al., arXiv:2504.07338 (2025), Eqs. 1, 3; Jones et al., Phys. Rev. B **87**,
  144103 (2013) / Fedorov–Tkatchenko (`Particles.QuantumDrudeOscillatorInvariants`,
  `ComplexAction.VanDerWaalsPolarizabilityScaling`); `Particles.DispersiveForceEntanglement`
  (arXiv:2407.04111).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.LennardJonesAxilrodTeller

open Physlib.QuantumMechanics.ComplexAction.Particles.QuantumDrudeOscillatorInvariants


/-- The **general `(n,m)` Lennard-Jones potential** (Eq. 1)
`E_LJ(r) = ε·(nm/(n−m))·[(1/n)(rₑ/r)ⁿ − (1/m)(rₑ/r)ᵐ]`, with `n > m` the repulsive/attractive exponents, `rₑ`
the equilibrium distance and `ε` the dissociation energy. The standard `12-6` potential is `n = 12`, `m = 6`. -/
noncomputable def ljPotential (ε rₑ r : ℝ) (n m : ℕ) : ℝ :=
  ε * ((n : ℝ) * m / ((n : ℝ) - m)) * (1 / (n : ℝ) * (rₑ / r) ^ n - 1 / (m : ℝ) * (rₑ / r) ^ m)

/-- **The Lennard-Jones well depth is exactly `−ε`** — `E_LJ(rₑ) = −ε`, the potential reaches minus the
dissociation energy at the equilibrium distance, for *every* exponent pair `n ≠ m` (both nonzero). The general
prefactor `nm/(n−m)` is fixed precisely so this holds independent of `(n,m)`. -/
lemma lj_at_re (ε rₑ : ℝ) (n m : ℕ) (hrₑ : rₑ ≠ 0)
    (hn : (n : ℝ) ≠ 0) (hm : (m : ℝ) ≠ 0) (hnm : (n : ℝ) - m ≠ 0) :
    ljPotential ε rₑ rₑ n m = -ε := by
  unfold ljPotential
  rw [div_self hrₑ, one_pow, one_pow]
  field_simp
  ring


/-- The **Axilrod-Teller-Muto angular factor** `1 + 3 cos θ₁ cos θ₂ cos θ₃` (Eq. 3, angle form) in the cosines of
the trimer's three interior angles; the full triple-dipole energy is `λ·(1 + 3c₁c₂c₃)/(r₁₂r₁₃r₂₃)³`. -/
def atmAngularFactor (c₁ c₂ c₃ : ℝ) : ℝ := 1 + 3 * c₁ * c₂ * c₃

/-- **An equilateral (close-packed) trimer is repulsive** — with all angles `60°` (`cos = 1/2`),
`atmAngularFactor = 11/8 > 0`, so for `λ > 0` the ATM energy is positive: three-body forces raise the energy of
compact geometries. -/
lemma atm_equilateral : atmAngularFactor (1 / 2) (1 / 2) (1 / 2) = 11 / 8 := by
  unfold atmAngularFactor; norm_num

/-- **A collinear trimer is attractive** — with one angle `180°` (`cos = −1`) and two `0°` (`cos = 1`),
`atmAngularFactor = −2 < 0`, so the ATM energy is negative: three-body forces *lower* the energy of linear
chains. The sign contrast with `atm_equilateral` is why repulsive ATM destabilizes fcc in favour of bcc/chains. -/
lemma atm_linear : atmAngularFactor (-1) 1 1 = -2 := by
  unfold atmAngularFactor; norm_num

/-- **The equilateral factor is strictly positive** (repulsive). -/
lemma atm_equilateral_pos : 0 < atmAngularFactor (1 / 2) (1 / 2) (1 / 2) := by
  rw [atm_equilateral]; norm_num

/-- **The collinear factor is strictly negative** (attractive). -/
lemma atm_linear_neg : atmAngularFactor (-1) 1 1 < 0 := by
  rw [atm_linear]; norm_num

/-- The **Axilrod-Teller-Muto energy** `λ·(1 + 3c₁c₂c₃)/(r₁₂r₁₃r₂₃)³` for a trimer with coupling `λ`, angle
cosines `cᵢ`, and pairwise distances. -/
noncomputable def atmEnergy (lam c₁ c₂ c₃ r₁₂ r₁₃ r₂₃ : ℝ) : ℝ :=
  lam * atmAngularFactor c₁ c₂ c₃ / (r₁₂ * r₁₃ * r₂₃) ^ 3

/-- **The ATM coupling is the QDO three-body coefficient** `λ = C₉ = 3/16 α₁³ℏω` — the phenomenological
Axilrod-Teller-Muto strength of the lattice paper is exactly the `C₉` three-body dispersion coefficient of
`QuantumDrudeOscillatorInvariants`, tying the crystal-stability three-body term to the microscopic QDO
polarizability. -/
lemma atmEnergy_coupling_eq_C9 (α₁ hω c₁ c₂ c₃ r₁₂ r₁₃ r₂₃ : ℝ) :
    atmEnergy (C9 α₁ hω) c₁ c₂ c₃ r₁₂ r₁₃ r₂₃
      = 3 / 16 * α₁ ^ 3 * hω * atmAngularFactor c₁ c₂ c₃ / (r₁₂ * r₁₃ * r₂₃) ^ 3 := by
  unfold atmEnergy C9; ring


/-- The **`c/a` ratio of the body-centred cubic (bcc) cell** along the Bain path: `1`. -/
def bccRatio : ℝ := 1

/-- The **`c/a` ratio of the face-centred cubic (fcc) cell** expressed as a body-centred tetragonal cell: `√2`.
The bct cell with `c/a ∈ [1, √2]` interpolates bcc to fcc along the martensitic Bain transformation. -/
noncomputable def fccRatio : ℝ := Real.sqrt 2

/-- **The fcc Bain ratio squares to `2`** — `(√2)² = 2`, the exact end-point of the `c/a` Bain path (bcc at
`c²/a² = 1`, fcc at `c²/a² = 2`). -/
lemma fccRatio_sq : fccRatio ^ 2 = 2 := by
  unfold fccRatio; rw [sq, Real.mul_self_sqrt]; norm_num

/-- **The bcc cell is more compact than the fcc cell along the Bain path** — `bccRatio < fccRatio`
(`1 < √2`): the martensitic transformation stretches the tetragonal `c/a` ratio from `1` to `√2`. -/
lemma bccRatio_lt_fccRatio : bccRatio < fccRatio := by
  unfold bccRatio fccRatio
  rw [show (1 : ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

end Physlib.QuantumMechanics.ComplexAction.Particles.LennardJonesAxilrodTeller

/-! ## Part II — the QDO invariants and the van der Waals radius scaling -/

namespace Physlib.QuantumMechanics.ComplexAction.Particles.QuantumDrudeOscillatorVanDerWaals

open Physlib.QuantumMechanics.ComplexAction.VanDerWaalsPolarizabilityScaling
open Physlib.QuantumMechanics.ComplexAction.Particles.QuantumDrudeOscillatorInvariants


/-- **The polarizability invariant holds for the QDO dipole polarizability** `α₁ = q²/(μω²)` — the
`9 α₁ α₃ = 20 α₂²` relation, evaluated on the concrete `qdoPolarizability` that drives the vdW radius law. -/
lemma polarizability_invariant_qdo (q μ ω L : ℝ) :
    9 * qdoPolarizability q μ ω * alphaOct (qdoPolarizability q μ ω) L
      = 20 * alphaQuad (qdoPolarizability q μ ω) L ^ 2 :=
  polarizability_invariant (qdoPolarizability q μ ω) L

/-- **The dispersion invariant holds for the QDO dipole polarizability** — `49 C₈² = 40 C₆ C₁₀` with
`α₁ = q²/(μω²)`. -/
lemma dispersion_invariant_qdo (q μ ω L hω : ℝ) :
    49 * C8 (qdoPolarizability q μ ω) L hω ^ 2
      = 40 * C6 (qdoPolarizability q μ ω) hω * C10 (qdoPolarizability q μ ω) L hω :=
  dispersion_invariant (qdoPolarizability q μ ω) L hω


/-- **The QDO `C₆` is the `−C₆/R⁶` coefficient of the van der Waals dispersion energy** — with `A = α₁²ℏω`,
`VanDerWaalsPolarizabilityScaling.dispersionEnergy (α₁²ℏω) R = −C₆/R⁶`, where `C₆` is the invariants module's
`¾ α₁² ℏω`. -/
lemma dispersionEnergy_eq_C6 (α₁ hω R : ℝ) :
    dispersionEnergy (α₁ ^ 2 * hω) R = -(C6 α₁ hω) / R ^ 6 := by
  unfold dispersionEnergy C6; ring


/-- **The van der Waals radius scales as `α^{1/7}` in the QDO polarizability** `R_vdW⁷ = C⁷ · q²/(μω²)` — the
`qdoPolarizability` satisfying the QDO invariants (§A) is exactly the `α` of the radius law. -/
lemma qdo_vdw_radius_seventh (C q μ ω : ℝ) (h : 0 ≤ qdoPolarizability q μ ω) :
    qmVdWRadius C (qdoPolarizability q μ ω) ^ 7 = C ^ 7 * qdoPolarizability q μ ω :=
  qmVdWRadius_pow_seven C (qdoPolarizability q μ ω) h

/-- **The octupole polarizability `α₃` sets a `α₃^{1/14}` radius scaling** — the multipole exponent
`multipoleVdWExponent 3 = 1/14`, the octupole counterpart of the dipole `1/7`. -/
lemma octupole_scaling_exponent : multipoleVdWExponent 3 = 1 / 14 := by
  unfold multipoleVdWExponent; norm_num

end Physlib.QuantumMechanics.ComplexAction.Particles.QuantumDrudeOscillatorVanDerWaals

/-! ## Part III — the Lennard-Jones lattice Hamiltonian's one microscopic origin -/

namespace Physlib.QuantumMechanics.ComplexAction.Particles.LennardJonesDispersion

open Physlib.QuantumMechanics.ComplexAction.Particles.LennardJonesAxilrodTeller
open Physlib.QuantumMechanics.ComplexAction.Particles.QuantumDrudeOscillatorInvariants
open Physlib.QuantumMechanics.ComplexAction.Particles.DispersiveForceEntanglement
open Physlib.QuantumMechanics.ComplexAction.VanDerWaalsPolarizabilityScaling


/-- The **repulsive `r^{−n}` part** of the Lennard-Jones potential. -/
noncomputable def ljRepulsive (ε rₑ r : ℝ) (n m : ℕ) : ℝ :=
  ε * ((n : ℝ) * m / ((n : ℝ) - m)) * (1 / (n : ℝ)) * (rₑ / r) ^ n

/-- The **attractive `r^{−m}` part** of the Lennard-Jones potential — for `m = 6` this is the London dispersion
tail. -/
noncomputable def ljAttractive (ε rₑ r : ℝ) (n m : ℕ) : ℝ :=
  ε * ((n : ℝ) * m / ((n : ℝ) - m)) * (1 / (m : ℝ)) * (rₑ / r) ^ m

/-- **The Lennard-Jones potential splits into repulsion minus attraction** `E_LJ = ljRepulsive − ljAttractive` —
the `r^{−n}` wall minus the `r^{−m}` dispersion tail. -/
lemma ljPotential_split (ε rₑ r : ℝ) (n m : ℕ) :
    ljPotential ε rₑ r n m = ljRepulsive ε rₑ r n m - ljAttractive ε rₑ r n m := by
  unfold ljPotential ljRepulsive ljAttractive; ring

/-- The **Lennard-Jones dispersion coefficient** `C₆^LJ = εn rₑ⁶/(n−6)` — the coefficient of the `r^{−6}`
attractive tail, read off for the standard `m = 6` exponent. -/
noncomputable def ljC6 (ε rₑ : ℝ) (n : ℕ) : ℝ := ε * (n : ℝ) * rₑ ^ 6 / ((n : ℝ) - 6)

/-- **The `m = 6` Lennard-Jones tail has the `−C₆/R⁶` dispersion form** `−ljAttractive = −C₆^LJ/r⁶` — the
attractive Lennard-Jones term is exactly a van der Waals dispersion energy, with coefficient `ljC6`. -/
lemma lj_tail_dispersion_form (ε rₑ r : ℝ) (n : ℕ) (hr : r ≠ 0) (hn6 : (n : ℝ) - 6 ≠ 0) :
    -ljAttractive ε rₑ r n 6 = -(ljC6 ε rₑ n) / r ^ 6 := by
  unfold ljAttractive ljC6
  rw [div_pow]
  push_cast
  field_simp

/-- **The Lennard-Jones tail equals the van der Waals `dispersionEnergy`** `−ljAttractive = dispersionEnergy
(4/3·C₆^LJ) r` — the attractive Lennard-Jones term coincides with `VanDerWaalsPolarizabilityScaling`'s
`−(3/4)A/R⁶` dispersion energy (`A = 4/3·ljC6`), identifying the LJ tail with the vdW dispersion. -/
lemma lj_tail_eq_vdw_dispersionEnergy (ε rₑ r : ℝ) (n : ℕ) (hr : r ≠ 0) (hn6 : (n : ℝ) - 6 ≠ 0) :
    -ljAttractive ε rₑ r n 6 = dispersionEnergy (4 / 3 * ljC6 ε rₑ n) r := by
  rw [lj_tail_dispersion_form ε rₑ r n hr hn6]
  unfold dispersionEnergy
  ring

/-- **When the LJ dispersion coefficient is the QDO `C₆`, the LJ tail is the QDO dispersion energy**
`−ljAttractive = −C₆/r⁶` — under `C₆^LJ = C₆ = ¾α₁²ℏω` the Lennard-Jones attractive term is precisely the QDO
van der Waals energy of `QuantumDrudeOscillatorInvariants`. -/
lemma lj_tail_is_qdo_C6 (ε rₑ r α₁ hω : ℝ) (n : ℕ) (hr : r ≠ 0) (hn6 : (n : ℝ) - 6 ≠ 0)
    (h : ljC6 ε rₑ n = C6 α₁ hω) :
    -ljAttractive ε rₑ r n 6 = -(C6 α₁ hω) / r ^ 6 := by
  rw [lj_tail_dispersion_form ε rₑ r n hr hn6, h]


/-- **The LJ tail coefficient and the ATM coupling are one QDO's `C₆` and `C₉`** `α₁·C₆ = 4·C₉` — the two-body
Lennard-Jones dispersion coefficient (`C₆`, §A) and the three-body Axilrod-Teller-Muto coupling
(`C₉ = atmEnergy` coupling) are dispersion coefficients of the *same* Quantum Drude Oscillator, related by its
three-body invariant. The whole cuboidal-lattice interaction has one microscopic origin. -/
lemma lattice_couplings_qdo_related (α₁ hω : ℝ) : α₁ * C6 α₁ hω = 4 * C9 α₁ hω :=
  threebody_invariant α₁ hω

/-- **The two-body tail binds, the three-body term is sign-variable** `dispersionCoeff 2 > 0` and
`dispersionCoeff 3 < 0` — the Lennard-Jones `−r^{−6}` two-body tail always binds (even-order dispersion), while
the Axilrod-Teller-Muto three-body coupling has the opposite (odd-order) sign, the same sign contrast the ATM
angular factor shows geometrically (`atm_equilateral` positive vs `atm_linear` negative). -/
lemma two_body_binds_three_body_signed :
    0 < dispersionCoeff 2 ∧ dispersionCoeff 3 < 0 :=
  ⟨dispersionCoeff_pos_even 2 (by decide), dispersionCoeff_neg_odd 3 (by decide)⟩

end Physlib.QuantumMechanics.ComplexAction.Particles.LennardJonesDispersion

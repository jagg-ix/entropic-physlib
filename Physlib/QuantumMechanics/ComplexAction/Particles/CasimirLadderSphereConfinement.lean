/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.AcharyaCanonicalSpinHelicity
public import Physlib.QuantumMechanics.ComplexAction.Particles.Su3WeylDimensionCasimir
public import Physlib.QuantumMechanics.ComplexAction.Particles.SuNGaugeSector
public import Physlib.QuantumMechanics.ComplexAction.Particles.Su3ConfinementPotential
public import Physlib.QuantumMechanics.ComplexAction.RiemannSphereBlochSL2CLinks
public import Physlib.QuantumMechanics.ComplexAction.Hopf.StokesSpinorIsomorphism
public import Physlib.QuantumMechanics.ComplexAction.Hopf.FibrationSpinorMap
public import Physlib.QuantumMechanics.ComplexAction.IcosahedralPoincareSphere
meta import Zil

/-!
# One Casimir ladder, one sphere of states: `su(2)` spin to `su(3)` confinement

Two existing towers meet here on exact identities.

**The Casimir ladder.** The fundamental quadratic Casimir `C_F(N) = (N²−1)/(2N)`
(`Su3WeylDimensionCasimir.fundamentalCasimirN`) evaluates the same formula on both gauge layers:

* **Rung `N = 2` is the spin Casimir.** The Pauli spin matrices `Sᵢ = ½σᵢ` of
  `AcharyaCanonicalSpinHelicity` satisfy `S² = ¾·1`, and `¾ = C_F(2)`
  (`spin_casimir_eq_ladder_rung_two`) — the same `σ` layer as the Dirac-Pauli dipole
  Hamiltonian of the QED grounding.
* **Rung `N = 3` is the colour-Coulomb coefficient.** The Cornell static quark potential
  `V(r) = −C_F αₛ/r + σr` takes its Coulomb strength from `C_F(3) = 4/3`, which is also the
  `SU(3)` weight-formula Casimir `casimir3 1 0` (`cornell_coulomb_eq_ladder_rung_three`).
* **The ladder strictly increases** (`casimirLadder_strictMono`): `(a−b)(ab+1) < 0` for
  `0 < a < b`, so colour couples stronger than spin, `C_F(2) = ¾ < 4/3 = C_F(3)`
  (`spin_rung_lt_color_rung`). The colour-singlet baryon `⋀³ℂ³ = C(3,3) = 1`
  (`SuNTensorDecomposition.sun_baryon_singlet`) is the spectrum-side face of confinement.

**The sphere of states.** The `su(2)` rung acts on a single geometric `S²` that three arcs
already build separately, and the affine-chart dictionary between them is proved here:

* the stereographic boundary coordinate lands on the Bloch sphere
  (`RiemannSphereBlochSL2CLinks.stereoInv_isBlochSphere`);
* the Hopf/Stokes base of the spinor `χ = (1, w)` is exactly the intensity times that
  stereographic Bloch vector, up to the `z`-reflection that encodes the north-versus-south
  projection convention (`hopfBase_eq_boundary_blochVector`):
  `(S₁, S₂, S₃) = (1+|w|²)·(x, y, −z)(π⁻¹ w)`;
* the icosahedral rotation group `A₅` of order `60` is the maximal finite rotation symmetry
  available on that sphere, with golden section `2cos(π/5) = φ`
  (`IcosahedralPoincareSphere`).

`casimir_ladder_sphere_confinement` records the junction as one statement.

**Honest layering.** Every leg is an exact identity or an inequality between exact values;
nothing dynamical is derived. The connection to the QED force-law arc and to the
Caticha–Maxwell causal arc is by shared carrier (the same Pauli `σ` layer, the same `S²`),
declared as such in the ZIL metadata — not a derivation of one sector from another. The
string tension `σ` and coupling `αₛ` stay free parameters; only the Casimir coefficient of
the Coulomb term is fixed by representation theory.

## References

* S. Saito, Front. Phys. 11 (2024) 1225334 (Stokes ↔ spin, Poincaré sphere).
* E. Eichten, K. Gottfried, T. Kinoshita, K.D. Lane, T.-M. Yan, Phys. Rev. D 17 (1978) 3090
  (Cornell potential).
* K.G. Wilson, Phys. Rev. D 10 (1974) 2445 (confinement, area law).
* F. Klein, *Vorlesungen über das Ikosaeder* (1884).
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.CasimirLadderSphereConfinement

open Physlib.QuantumMechanics.ComplexAction.AcharyaCanonicalSpinHelicity
open Physlib.QuantumMechanics.ComplexAction.Particles.Su3WeylDimensionCasimir
open Physlib.QuantumMechanics.ComplexAction.Particles.SuNGaugeSector
open Physlib.QuantumMechanics.ComplexAction.Particles.Su3ConfinementPotential
open Physlib.QuantumMechanics.ComplexAction.Particles.SuNTensorDecomposition
open Physlib.QuantumMechanics.ComplexAction.RiemannSphereBlochSL2CLinks
open Physlib.QuantumMechanics.ComplexAction.LorenzQubitBlochDynamics
open Physlib.QuantumMechanics.ComplexAction.Hopf.StokesSpinorIsomorphism
open Physlib.QuantumMechanics.ComplexAction.Hopf.FibrationSpinorMap
open Physlib.QuantumMechanics.ComplexAction.IcosahedralPoincareSphere
open Physlib.Mathematics.Geometry.StereographicRiemannSphere

/-! ## §A — The Casimir ladder: rung 2 is spin, rung 3 is the colour Coulomb strength -/

/-- **The spin Casimir is rung two of the fundamental Casimir ladder**
`S₁² + S₂² + S₃² = C_F(2)·1` with `C_F(2) = (2²−1)/(2·2) = ¾`: the `s(s+1)` value of the
Pauli spin matrices is the `N = 2` evaluation of the same formula whose `N = 3` evaluation
scales the colour-Coulomb term. -/
theorem spin_casimir_eq_ladder_rung_two :
    spin1 * spin1 + spin2 * spin2 + spin3 * spin3 =
      ((fundamentalCasimirN 2 : ℚ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have h : ((fundamentalCasimirN 2 : ℚ) : ℂ) = (3 / 4 : ℂ) := by
    rw [su2_fund_casimir]; norm_num
  rw [h]
  exact spin_casimir

/-- **The Cornell Coulomb coefficient is rung three of the fundamental Casimir ladder**:
evaluating the Cornell potential at `C_F = fundamentalCasimirN 3` gives exactly the
`−(casimir3 1 0)·αₛ/r + σr` form — the coefficient fixed by the `SU(3)` weight-formula
Casimir of the fundamental `(p,q) = (1,0)`. -/
theorem cornell_coulomb_eq_ladder_rung_three (alpha sigma r : ℝ) :
    cornellPotential ((fundamentalCasimirN 3 : ℚ) : ℝ) alpha sigma r
      = -((casimir3 1 0 : ℚ) : ℝ) * alpha / r + sigma * r := by
  have h : ((fundamentalCasimirN 3 : ℚ) : ℝ) = ((casimir3 1 0 : ℚ) : ℝ) := by
    rw [fundamentalCasimirN_three, casimir3_fundamental]
  rw [cornellPotential, h]

/-- **The fundamental Casimir ladder is strictly increasing** `0 < a < b → C_F(a) < C_F(b)`:
from `(a²−1)·2b < (b²−1)·2a ↔ (b−a)(ab+1) > 0`. -/
theorem casimirLadder_strictMono {a b : ℚ} (ha : 0 < a) (hab : a < b) :
    fundamentalCasimirN a < fundamentalCasimirN b := by
  have hb : 0 < b := ha.trans hab
  rw [fundamentalCasimirN, fundamentalCasimirN,
    div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos (sub_pos.mpr hab) (show (0 : ℚ) < a * b + 1 by positivity)]

/-- **Colour couples stronger than spin** `C_F(2) = ¾ < 4/3 = C_F(3)`: the two rungs used in
this file, ordered by the ladder monotonicity. -/
theorem spin_rung_lt_color_rung :
    fundamentalCasimirN 2 < fundamentalCasimirN 3 :=
  casimirLadder_strictMono (by norm_num) (by norm_num)

/-! ## §B — The sphere of states: Hopf base = stereographic boundary Bloch vector -/

/-- **The Hopf intensity of the affine-chart spinor** `S₀(1, w) = |w|² + 1` — exactly the
stereographic denominator of `stereoInv w`. -/
lemma hopfIntensity_projective (w : ℂ) :
    hopfIntensity ![1, w] = ((Complex.normSq w + 1 : ℝ) : ℂ) := by
  rw [hopfIntensity, stokesS0_eq_normSq]
  norm_cast
  simp [Complex.normSq_one]
  ring

/-- **The Hopf base is the stereographic boundary Bloch vector**
`(S₁, S₂, S₃)(1, w) = (1 + |w|²) · (x, y, −z)(π⁻¹ w)`: the Stokes/Hopf image of the
affine-chart spinor `χ = (1, w)` equals the intensity times the Bloch vector that
`RiemannSphereBlochSL2CLinks` assigns to the boundary coordinate `w`, with the single
`z`-reflection recording that the spinor convention puts `w = 0` at spin-up while
`stereoInv` projects from the north pole. One sphere, three constructions. -/
theorem hopfBase_eq_boundary_blochVector (w : ℂ) (i : Fin 3) :
    hopfBase ![1, w] i
      = hopfIntensity ![1, w] * ((![(1 : ℝ), 1, -1] i * blochVectorOfBoundary w i : ℝ) : ℂ) := by
  have hden : Complex.normSq w + 1 ≠ 0 :=
    (add_pos_of_nonneg_of_pos (Complex.normSq_nonneg w) one_pos).ne'
  fin_cases i
  · -- `S₁ = (1+|w|²)·x(π⁻¹w) = 2 Re w`
    show stokesS (Sum.inr 0) ![1, w]
        = hopfIntensity ![1, w] * ((![(1 : ℝ), 1, -1] 0 * blochVectorOfBoundary w 0 : ℝ) : ℂ)
    rw [stokesS1_apply, hopfIntensity_projective]
    simp only [blochVectorOfBoundary, stereoInv, Matrix.cons_val_zero, Matrix.cons_val_one,
      star_one, one_mul, mul_one]
    rw [show (star w : ℂ) = (starRingEnd ℂ) w from rfl, Complex.add_conj,
      ← Complex.ofReal_mul, Complex.ofReal_inj, ← mul_div_assoc,
      mul_div_cancel_left₀ _ hden]
  · -- `S₂ = (1+|w|²)·y(π⁻¹w) = 2 Im w`
    show stokesS (Sum.inr 1) ![1, w]
        = hopfIntensity ![1, w] * ((![(1 : ℝ), 1, -1] 1 * blochVectorOfBoundary w 1 : ℝ) : ℂ)
    rw [stokesS2_apply, hopfIntensity_projective]
    simp only [blochVectorOfBoundary, stereoInv, Matrix.cons_val_zero, Matrix.cons_val_one,
      star_one, one_mul, mul_one]
    rw [show (star w : ℂ) = (starRingEnd ℂ) w from rfl]
    have hsub : Complex.I * ((starRingEnd ℂ) w - w) = ((2 * w.im : ℝ) : ℂ) := by
      have h2 : (starRingEnd ℂ) w - w = -((2 * w.im : ℝ) * Complex.I) := by
        rw [← Complex.sub_conj]; ring
      rw [h2, show Complex.I * -((2 * w.im : ℝ) * Complex.I)
          = -(((2 * w.im : ℝ) : ℂ) * (Complex.I * Complex.I)) from by ring,
        Complex.I_mul_I]
      ring
    rw [hsub, ← Complex.ofReal_mul, Complex.ofReal_inj, ← mul_div_assoc,
      mul_div_cancel_left₀ _ hden]
  · -- `S₃ = (1+|w|²)·(−z)(π⁻¹w) = 1 − |w|²`
    show stokesS (Sum.inr 2) ![1, w]
        = hopfIntensity ![1, w] * ((![(1 : ℝ), 1, -1] 2 * blochVectorOfBoundary w 2 : ℝ) : ℂ)
    rw [stokesS3_apply, hopfIntensity_projective]
    simp only [blochVectorOfBoundary, stereoInv, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, star_one, mul_one]
    rw [show (star w : ℂ) = (starRingEnd ℂ) w from rfl, ← Complex.normSq_eq_conj_mul_self,
      show ((1 : ℂ) - (Complex.normSq w : ℂ)) = ((1 - Complex.normSq w : ℝ) : ℂ) from by
        push_cast; ring,
      ← Complex.ofReal_mul, Complex.ofReal_inj]
    rw [neg_one_mul, mul_neg, ← mul_div_assoc, mul_div_cancel_left₀ _ hden]
    ring

/-! ## §C — The junction -/

/-- **One Casimir ladder and one sphere of states join `su(2)` spin to `su(3)` confinement**:
(i) the spin Casimir is ladder rung two; (ii) the Cornell Coulomb coefficient is ladder rung
three, equal to the `SU(3)` weight Casimir; (iii) the ladder strictly increases between them;
(iv) the baryon is the colour singlet `C(3,3) = 1`; (v) every boundary coordinate lands on the
Bloch sphere; (vi) the Hopf base of the affine-chart spinor is that boundary Bloch vector up to
the polar convention; (vii)–(viii) the sphere carries the icosahedral `A₅` of order `60` with
golden section `2cos(π/5) = φ`. -/
theorem casimir_ladder_sphere_confinement (alpha sigma r : ℝ) :
    (spin1 * spin1 + spin2 * spin2 + spin3 * spin3
        = ((fundamentalCasimirN 2 : ℚ) : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ))
    ∧ (cornellPotential ((fundamentalCasimirN 3 : ℚ) : ℝ) alpha sigma r
        = -((casimir3 1 0 : ℚ) : ℝ) * alpha / r + sigma * r)
    ∧ fundamentalCasimirN 2 < fundamentalCasimirN 3
    ∧ Nat.choose 3 3 = 1
    ∧ (∀ v : ℂ, BlochSphere (blochVectorOfBoundary v))
    ∧ (∀ (v : ℂ) (i : Fin 3), hopfBase ![1, v] i
        = hopfIntensity ![1, v] * ((![(1 : ℝ), 1, -1] i * blochVectorOfBoundary v i : ℝ) : ℂ))
    ∧ Nat.card (alternatingGroup (Fin 5)) = 60
    ∧ 2 * Real.cos (Real.pi / 5) = Real.goldenRatio :=
  ⟨spin_casimir_eq_ladder_rung_two,
   cornell_coulomb_eq_ladder_rung_three alpha sigma r,
   spin_rung_lt_color_rung,
   sun_baryon_singlet 3,
   fun v => stereoInv_isBlochSphere v,
   fun v i => hopfBase_eq_boundary_blochVector v i,
   icosahedralRotation_card,
   two_cos_pi_div_five_eq_goldenRatio⟩

/-! ## ZIL metadata -/

/- ZIL-BEGIN -/

zil attach spin_casimir_eq_ladder_rung_two where
  formalizes @ "claim:su2-spin-casimir-is-rung-two-of-the-fundamental-casimir-ladder",
  supported_by @ "paper:gell-mann-1962-symmetries-of-baryons-and-mesons",
  caveat @ "claim:exact-representation-theory-identity-shares-the-pauli-sigma-layer-with-the-dirac-pauli-qed-grounding"

zil attach cornell_coulomb_eq_ladder_rung_three where
  formalizes @ "claim:cornell-coulomb-coefficient-is-rung-three-of-the-fundamental-casimir-ladder",
  supported_by @ "paper:eichten-gottfried-kinoshita-lane-yan-1978-cornell-potential",
  supported_by @ "measurement:charmonium-and-bottomonium-spectroscopy-cornell-fits",
  caveat @ "claim:string-tension-and-alpha-s-remain-free-parameters-only-the-casimir-coefficient-is-fixed"

zil attach spin_rung_lt_color_rung where
  formalizes @ "claim:fundamental-casimir-ladder-strictly-increases-colour-couples-stronger-than-spin",
  supported_by @ "paper:wilson-1974-confinement-of-quarks",
  caveat @ "claim:ordering-of-casimir-coefficients-not-of-running-couplings"

zil_theorem_intent hopfBase_eq_boundary_blochVector where
  at_level bridge_theorem
  must_mention [hopfBase, blochVectorOfBoundary]

zil attach hopfBase_eq_boundary_blochVector where
  formalizes @ "claim:hopf-base-is-the-stereographic-boundary-bloch-vector-up-to-polar-convention",
  supported_by @ "paper:saito-2024-stokes-spin-isomorphism",
  caveat @ "claim:z-reflection-encodes-north-versus-south-pole-stereographic-convention",
  caveat @ "claim:stated-on-the-affine-chart-spinor-one-w-the-fiber-at-chi-zero-equals-zero-is-the-point-at-infinity"

zil_theorem_intent casimir_ladder_sphere_confinement where
  at_level bridge_theorem
  must_mention [cornellPotential, BlochSphere]

zil attach casimir_ladder_sphere_confinement where
  formalizes @ "claim:one-fundamental-casimir-ladder-and-one-bloch-sphere-join-qed-spin-to-qcd-confinement",
  requires @ "claim:su2-spin-casimir-is-rung-two-of-the-fundamental-casimir-ladder",
  requires @ "claim:cornell-coulomb-coefficient-is-rung-three-of-the-fundamental-casimir-ladder",
  requires @ "claim:fundamental-casimir-ladder-strictly-increases-colour-couples-stronger-than-spin",
  requires @ "claim:hopf-base-is-the-stereographic-boundary-bloch-vector-up-to-polar-convention",
  supported_by @ "paper:klein-1884-lectures-on-the-icosahedron",
  caveat @ "claim:conjunction-of-exact-identities-nothing-dynamical-derived-across-sectors",
  caveat @ "claim:connects-to-the-qed-force-law-and-caticha-maxwell-arcs-by-shared-carrier-same-sigma-layer-same-sphere-not-by-derivation"

zil_file_contract physlib.casimirLadderSphereConfinement where
  promises "The su(2)-to-su(3) junction on exact identities: the Pauli spin Casimir three-quarters is the N equals 2 rung of the fundamental Casimir ladder N squared minus one over twice N, the Cornell colour-Coulomb coefficient four-thirds is the N equals 3 rung and equals the SU(3) weight-formula Casimir of the fundamental representation, the ladder strictly increases so colour couples stronger than spin, the baryon is the colour singlet, and the sphere the su(2) rung acts on is simultaneously the stereographic Riemann-sphere boundary Bloch vector and the Hopf-Stokes base of the affine-chart spinor up to the polar convention, carrying the icosahedral A5 with golden section two cos pi over five."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.AcharyaCanonicalSpinHelicity.spin1",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.Su3WeylDimensionCasimir.fundamentalCasimirN",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.Su3ConfinementPotential.cornellPotential",
    "lean:Physlib.QuantumMechanics.ComplexAction.RiemannSphereBlochSL2CLinks.blochVectorOfBoundary",
    "lean:Physlib.QuantumMechanics.ComplexAction.Hopf.FibrationSpinorMap.hopfBase",
    "lean:Physlib.QuantumMechanics.ComplexAction.IcosahedralPoincareSphere.icosahedralRotation_card"]
  forbids_substitutes ["a derivation of the string tension or of alpha-s, which stay free parameters",
    "running-coupling statements, ordered here only at the level of Casimir coefficients",
    "a derivation of one sector from another - the shared sigma layer and shared sphere are structural",
    "the chi-zero-equals-zero fiber of the Hopf chart, which is the point at infinity of the boundary coordinate"]
  witnessed_by [spin_casimir_eq_ladder_rung_two, cornell_coulomb_eq_ladder_rung_three,
    casimirLadder_strictMono, spin_rung_lt_color_rung, hopfIntensity_projective,
    hopfBase_eq_boundary_blochVector, casimir_ladder_sphere_confinement]

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.Particles.CasimirLadderSphereConfinement

end

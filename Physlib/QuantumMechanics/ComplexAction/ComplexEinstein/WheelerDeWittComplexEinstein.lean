/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.WheelerDeWittLusanna
public import Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ComplexEinsteinScalarConstraint
public import Physlib.QFT.PathIntegral.Lorentzian

meta import Zil

/-!
# The Wheeler–DeWitt equation is the complex Einstein scalar constraint

Links the **Wheeler–DeWitt equation** (`ComplexEinstein.WheelerDeWittLusanna`, the quantized ADM Hamiltonian constraint)
to the **complex Einstein scalar constraint** (`CanonicalTetradGravity.ComplexEinsteinScalarConstraint`,
`ComplexEinstein.ComplexMassEinsteinEquations`), closing the loop of the complex-gravity arc.

Sourcing the Wheeler–DeWitt Hamiltonian operator by Nagao–Nielsen complex-mass matter — the real part of
the complex Einstein energy `Re E_C = m_R c²` in the gravitational constraint, the imaginary part
`Im E_C = m_I c²` as the imaginary Hamiltonian `Ĥ_I` — the Wheeler–DeWitt equation

  `(ℋ − κ·Re E_C − i·κ·Im E_C) Ψ = 0`

for a non-trivial wavefunctional `Ψ ≠ 0` is **exactly** the complex sourced ADM scalar constraint
`ℂ(ℋ) = κ E_C` (`wheelerDeWitt_eq_complexSourcedScalarConstraint`). Consequently a Wheeler–DeWitt physical
state forces **reversible matter** `m_I = 0` (`wheelerDeWitt_forces_reversible`) — the *same* reality
obstruction that the complex Einstein equation imposes
(`complexSourcedScalarConstraint_reality`): a real classical geometry admits only real-mass matter.

So the Wheeler–DeWitt equation, the complex Einstein scalar constraint, and the complex Einstein energy
are one structure: the quantized constraint annihilating `Ψ` is the complexified `G_{nn}` equation, real
exactly when the matter is reversible.

* **§A — Wheeler–DeWitt = complex sourced scalar constraint**
  (`wheelerDeWitt_eq_complexSourcedScalarConstraint`).
* **§B — a Wheeler–DeWitt state forces reversible matter** (`wheelerDeWitt_forces_reversible`).
* **§C — the assembly** (`wheelerDeWitt_isComplexEinsteinScalarConstraint`).

## Ooguri–Vafa–Verlinde flux wavefunction

The finite period carrier below isolates the exact algebra in H. Ooguri, C. Vafa,
and E. Verlinde, *Hartle–Hawking Wave-Function for Flux Compactifications: the
Entropic Principle* (2005):

* **§D — flux composition.** The superpotential
  `W = ∑ᴵ (qᴵ Xᴵ − pᴵ Fᴵ)` is additive in the finite real flux-coordinate data, and its
  real-basis insertion is multiplicative.
* **§E — semiclassical Hartle–Hawking density.** The squared norm of the
  Kähler-prefactored state is exactly Eq. (3.8), and the radial reduction Eq. (3.9)
  has the unique peak `R = M / 2` with value `exp (π M² / 4)`.
* **§F — OSV polarization.** The flux wavefunction of Eqs. (6.7–6.8) has
  squared norm equal to the OSV Laplace integrand; the integrated equality is
  therefore proved without duplicating measure theory. The attractor equation
  `q = −∂φ F` makes the entropy Legendre transform stationary.
* **§G — polarization independence.** The holomorphic flux wave of Eq. (5.6)
  and the real-polarization insertion have the same norm square, so the
  semiclassical probability is independent of these two presentations.
* **§H — full finite flux family.** The scalar OSV API is lifted to arbitrary
  finite electric/magnetic flux vectors and proved to specialize exactly to the
  one-component carrier.
* **§I — supersymmetric WDW implication.** A bundled supercharge satisfying
  `Q² = H` sends every BPS state `Qψ = 0` to a Wheeler–DeWitt state `Hψ = 0`.

The scope is deliberately narrower than the physical conjecture. The periods,
Kähler potential, and topological-string wavefunction are supplied carriers; this
module does not construct Calabi–Yau cohomology, prove the all-genus OSV/microscopic
index conjecture, or identify the Euclidean radial saddle with Lorentzian
cosmological evolution. The flux insertion corresponds to a *negative* imaginary
action in `lorentzianKernel`, hence an enhancement rather than a dissipative
contraction.

## References

* B. S. DeWitt (Wheeler–DeWitt); K. Nagao, H. B. Nielsen (complex mass). Repo carriers:
  `ComplexEinstein.WheelerDeWittLusanna` (`WheelerDeWitt`, `wheelerDeWitt_iff_of_ne`),
  `CanonicalTetradGravity.ComplexEinsteinScalarConstraint` (`complexSourcedScalarConstraint`,
  `complexSourcedScalarConstraint_iff`, `complexSourcedScalarConstraint_reality`),
  `ComplexEinstein.ComplexMassEinsteinEquations` (`complexEinsteinEnergy`).
* H. Ooguri, C. Vafa, E. Verlinde, *Hartle–Hawking Wave-Function for Flux
  Compactifications: the Entropic Principle* (2005), Eqs. (2.9), (3.8), (3.9),
  and (6.2)–(6.8).


-/

set_option autoImplicit false
noncomputable section

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.WheelerDeWittComplexEinstein

open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.TetradADMGravity
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.WheelerDeWittLusanna
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations
open Physlib.QuantumMechanics.ComplexAction.CanonicalTetradGravity.ComplexEinsteinScalarConstraint
open Physlib.QFT.PathIntegral
open BigOperators MeasureTheory Complex

variable {d : ℕ}


/-- **[The Wheeler–DeWitt equation is the complex sourced scalar constraint].** With the gravitational
Hamiltonian operator sourced by the complex Einstein energy — `Ĥ_R = ℋ − κ·Re E_C` (the total constraint
`ℋ − κ m_R c²`), `Ĥ_I = κ·Im E_C = κ m_I c²` — the Wheeler–DeWitt equation `(Ĥ_R − iĤ_I)Ψ = 0` for a
non-trivial wavefunctional `Ψ ≠ 0` is *exactly* the complex sourced ADM scalar constraint
`ℂ(ℋ) = κ E_C` (`complexSourcedScalarConstraint`): the quantized constraint annihilating `Ψ` is the
complexified `G_{nn} = κ T_{nn}` Einstein equation. -/
lemma wheelerDeWitt_eq_complexSourcedScalarConstraint (R3 KdotK m_R m_I c κ : ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (Ψ : ℂ) (hΨ : Ψ ≠ 0) :
    WheelerDeWitt (hamiltonianConstraint R3 KdotK K - κ * (complexEinsteinEnergy m_R m_I c).re)
        (κ * (complexEinsteinEnergy m_R m_I c).im) Ψ
      ↔ complexSourcedScalarConstraint R3 KdotK m_R m_I c κ K := by
  rw [wheelerDeWitt_iff_of_ne _ _ Ψ hΨ, complexEinsteinEnergy_re, complexEinsteinEnergy_im,
    sub_eq_zero, complexSourcedScalarConstraint_iff]


/-- **[A Wheeler–DeWitt physical state forces reversible matter] `m_I = 0`.** A non-trivial Wheeler–DeWitt
state sourced by complex-mass matter (`κ ≠ 0`, `c ≠ 0`) forces the imaginary (entropic) mass to vanish —
the *same* reality obstruction as the complex Einstein equation
(`complexSourcedScalarConstraint_reality`): the quantized real ADM geometry admits only reversible
(real-mass) matter. -/
lemma wheelerDeWitt_forces_reversible (R3 KdotK m_R m_I c κ : ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (Ψ : ℂ) (hΨ : Ψ ≠ 0) (hκ : κ ≠ 0) (hc : c ≠ 0)
    (h : WheelerDeWitt (hamiltonianConstraint R3 KdotK K - κ * (complexEinsteinEnergy m_R m_I c).re)
          (κ * (complexEinsteinEnergy m_R m_I c).im) Ψ) :
    m_I = 0 :=
  complexSourcedScalarConstraint_reality R3 KdotK m_R m_I c κ K hκ hc
    ((wheelerDeWitt_eq_complexSourcedScalarConstraint R3 KdotK m_R m_I c κ K Ψ hΨ).mp h)


/-- **[The Wheeler–DeWitt equation is the complex Einstein scalar constraint, real ⟺ reversible matter].**
The single statement of the complex-gravity loop. For a non-trivial wavefunctional `Ψ ≠ 0` sourced by
Nagao–Nielsen complex-mass matter (`κ ≠ 0`, `c ≠ 0`), with the Wheeler–DeWitt Hamiltonian operator
`Ĥ_R = ℋ − κ·Re E_C`, `Ĥ_I = κ·Im E_C`:

1. the **Wheeler–DeWitt equation `(Ĥ_R − iĤ_I)Ψ = 0` is exactly the complex sourced ADM scalar
   constraint** `ℂ(ℋ) = κ E_C` — the quantized constraint annihilating `Ψ` is the complexified
   `G_{nn} = κ T_{nn}` Einstein equation;
2. equivalently, it is the **real ADM constraint sourced by the rest energy** `ℋ = κ m_R c²` *together
   with* the **vanishing of the imaginary (entropic) source** `κ m_I c² = 0`;
3. hence a **Wheeler–DeWitt physical state forces reversible matter** `m_I = 0` — a real quantized ADM
   geometry admits only real-mass matter.

The quantized ADM Hamiltonian constraint (`ComplexEinstein.WheelerDeWittLusanna`), the complex Einstein scalar constraint
(`CanonicalTetradGravity.ComplexEinsteinScalarConstraint`), and the complex Einstein energy
(`ComplexEinstein.ComplexMassEinsteinEquations`) are one structure: the Wheeler–DeWitt equation is the complexified
`G_{nn}` equation, real exactly when the matter is reversible. -/
lemma wheelerDeWitt_isComplexEinsteinScalarConstraint (R3 KdotK m_R m_I c κ : ℝ)
    (K : Matrix (Fin d) (Fin d) ℝ) (Ψ : ℂ) (hΨ : Ψ ≠ 0) (hκ : κ ≠ 0) (hc : c ≠ 0) :
    (WheelerDeWitt (hamiltonianConstraint R3 KdotK K - κ * (complexEinsteinEnergy m_R m_I c).re)
        (κ * (complexEinsteinEnergy m_R m_I c).im) Ψ
      ↔ complexSourcedScalarConstraint R3 KdotK m_R m_I c κ K)
    ∧ (WheelerDeWitt (hamiltonianConstraint R3 KdotK K - κ * (complexEinsteinEnergy m_R m_I c).re)
        (κ * (complexEinsteinEnergy m_R m_I c).im) Ψ
      ↔ hamiltonianConstraint R3 KdotK K = κ * (m_R * c ^ 2) ∧ κ * (m_I * c ^ 2) = 0)
    ∧ (WheelerDeWitt (hamiltonianConstraint R3 KdotK K - κ * (complexEinsteinEnergy m_R m_I c).re)
        (κ * (complexEinsteinEnergy m_R m_I c).im) Ψ → m_I = 0) :=
  let hEq := wheelerDeWitt_eq_complexSourcedScalarConstraint R3 KdotK m_R m_I c κ K Ψ hΨ
  ⟨hEq, hEq.trans (complexSourcedScalarConstraint_iff R3 KdotK m_R m_I c κ K),
    fun h => wheelerDeWitt_forces_reversible R3 KdotK m_R m_I c κ K Ψ hΨ hκ hc h⟩

/-! ## Ooguri–Vafa–Verlinde flux wavefunction -/

/-- The finite symplectic flux superpotential
`W = ∑ᴵ (qᴵ Xᴵ − pᴵ Fᴵ)` of Ooguri–Vafa–Verlinde Eq. (2.9).

The periods `X` and `F` are explicit inputs. This definition does not construct a
Calabi–Yau period map. -/
def fluxSuperpotential {n : ℕ} (q p : Fin n → ℝ) (X F : Fin n → ℂ) : ℂ :=
  ∑ i, ((q i : ℂ) * X i - (p i : ℂ) * F i)

/-- Flux-sector superpotentials add under addition of the electric and magnetic
flux vectors. -/
@[zil_level bridge_theorem]
lemma fluxSuperpotential_add {n : ℕ} (q q' p p' : Fin n → ℝ) (X F : Fin n → ℂ) :
    fluxSuperpotential (q + q') (p + p') X F =
      fluxSuperpotential q p X F + fluxSuperpotential q' p' X F := by
  unfold fluxSuperpotential
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Pi.add_apply, ofReal_add]
  ring

/-- The real-polarization flux insertion in Ooguri–Vafa–Verlinde Eq. (3.8).
Because `W - star W = 2 i Im W`, this exponential is real and positive. -/
def fluxInsertion (W : ℂ) : ℂ :=
  Complex.exp (-Complex.I * (Real.pi : ℂ) / 4 * (W - (starRingEnd ℂ) W))

/-- The flux insertion is `exp ((π/2) Im W)`. -/
lemma fluxInsertion_eq_exp_im (W : ℂ) :
    fluxInsertion W = Complex.exp ((Real.pi / 2 * W.im : ℝ) : ℂ) := by
  unfold fluxInsertion
  congr 1
  apply Complex.ext
  · simp
    ring
  · simp

/-- Independent additive flux sectors multiply at the wavefunction level. -/
@[zil_level bridge_theorem]
lemma fluxInsertion_add (W Z : ℂ) :
    fluxInsertion (W + Z) = fluxInsertion W * fluxInsertion Z := by
  rw [fluxInsertion_eq_exp_im, fluxInsertion_eq_exp_im, fluxInsertion_eq_exp_im]
  rw [add_im]
  rw [show Real.pi / 2 * (W.im + Z.im) =
      Real.pi / 2 * W.im + Real.pi / 2 * Z.im by ring]
  simpa only [ofReal_add] using
    (Complex.exp_add ((Real.pi / 2 * W.im : ℝ) : ℂ)
      ((Real.pi / 2 * Z.im : ℝ) : ℂ))

/-- The OVV flux insertion is the repository's complex-action kernel with zero
real action, unit `ℏ`, and imaginary action `S_I = −(π/2) Im W`.

The minus sign is load-bearing: for positive `Im W` this is exponential
enhancement, not ordinary positive-`S_I` dissipation. -/
@[zil_level bridge_theorem]
lemma fluxInsertion_eq_lorentzianKernel (W : ℂ) :
    fluxInsertion W = lorentzianKernel 0 (-(Real.pi / 2 * W.im)) 1 := by
  rw [fluxInsertion_eq_exp_im]
  unfold lorentzianKernel
  congr 1
  push_cast
  ring

/-- The squared flux insertion is `exp (π Im W)`. -/
lemma fluxInsertion_normSq (W : ℂ) :
    Complex.normSq (fluxInsertion W) = Real.exp (Real.pi * W.im) := by
  rw [fluxInsertion_eq_exp_im, Complex.normSq_eq_norm_sq, Complex.norm_exp]
  simp only [ofReal_re, pow_two, ← Real.exp_add]
  congr 1
  ring

/-- Flux-dependent factor formed from the finite symplectic period carrier. -/
def fluxSectorWeight {n : ℕ} (q p : Fin n → ℝ) (X F : Fin n → ℂ) : ℂ :=
  fluxInsertion (fluxSuperpotential q p X F)

/-- Addition of flux data becomes multiplication of flux-sector weights. -/
@[zil_level bridge_theorem]
lemma fluxSectorWeight_add {n : ℕ} (q q' p p' : Fin n → ℝ) (X F : Fin n → ℂ) :
    fluxSectorWeight (q + q') (p + p') X F =
      fluxSectorWeight q p X F * fluxSectorWeight q' p' X F := by
  rw [fluxSectorWeight, fluxSectorWeight, fluxSectorWeight,
    fluxSuperpotential_add, fluxInsertion_add]

/-- The Kähler-prefactored semiclassical Hartle–Hawking flux state underlying
OVV Eq. (3.8). -/
def hartleHawkingFluxState (K : ℝ) (W : ℂ) : ℂ :=
  (Real.exp (-(Real.pi / 8) * K) : ℂ) * fluxInsertion W

/-- **OVV Eq. (3.8).** The state has probability density
`exp (−πK/4 + π Im W)`, exactly the real form of
`exp (−πK/4 − iπ(W−W̄)/2)`. -/
@[zil_level bridge_theorem]
lemma hartleHawkingFluxState_normSq (K : ℝ) (W : ℂ) :
    Complex.normSq (hartleHawkingFluxState K W) =
      Real.exp (-(Real.pi / 4) * K + Real.pi * W.im) := by
  unfold hartleHawkingFluxState
  rw [Complex.normSq_mul, Complex.normSq_ofReal,
    fluxInsertion_normSq, ← Real.exp_add, ← Real.exp_add]
  congr 1
  ring

/-- The radial exponent `−π(R²−MR)` of OVV Eq. (3.9). -/
def radialEntropyExponent (M R : ℝ) : ℝ := -Real.pi * (R ^ 2 - M * R)

/-- Completion of the square exposes the entropy term and the radial deficit. -/
lemma radialEntropyExponent_completeSquare (M R : ℝ) :
    radialEntropyExponent M R =
      Real.pi * M ^ 2 / 4 - Real.pi * (R - M / 2) ^ 2 := by
  unfold radialEntropyExponent
  ring

/-- The radial exponent is maximal at the attractor radius `R = M/2`. -/
lemma radialEntropyExponent_le_attractor (M R : ℝ) :
    radialEntropyExponent M R ≤ radialEntropyExponent M (M / 2) := by
  rw [radialEntropyExponent_completeSquare, radialEntropyExponent_completeSquare]
  nlinarith [Real.pi_pos, sq_nonneg (R - M / 2)]

/-- The radial extremum is unique: equality with the attractor value holds exactly
at `R = M/2`. -/
@[zil_level bridge_theorem]
lemma radialEntropyExponent_eq_attractor_iff (M R : ℝ) :
    radialEntropyExponent M R = radialEntropyExponent M (M / 2) ↔ R = M / 2 := by
  rw [radialEntropyExponent_completeSquare, radialEntropyExponent_completeSquare]
  constructor
  · intro h
    have hmul : Real.pi * (R - M / 2) ^ 2 = 0 := by
      nlinarith
    have hsquare : (R - M / 2) ^ 2 = 0 :=
      (mul_eq_zero.mp hmul).resolve_left (ne_of_gt Real.pi_pos)
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsquare)
  · rintro rfl
    rfl

/-- The radial semiclassical probability appearing in OVV Eq. (3.9). -/
def radialHartleHawkingProbability (M R : ℝ) : ℝ :=
  Real.exp (radialEntropyExponent M R)

/-- The radial probability is bounded above by its attractor value. -/
lemma radialHartleHawkingProbability_le_attractor (M R : ℝ) :
    radialHartleHawkingProbability M R ≤ radialHartleHawkingProbability M (M / 2) := by
  exact Real.exp_le_exp.mpr (radialEntropyExponent_le_attractor M R)

/-- **Unique OVV radial saddle.** The probability reaches its attractor value if
and only if `R = M/2`. -/
@[zil_level bridge_theorem]
lemma radialHartleHawkingProbability_eq_attractor_iff (M R : ℝ) :
    radialHartleHawkingProbability M R = radialHartleHawkingProbability M (M / 2) ↔
      R = M / 2 := by
  simp only [radialHartleHawkingProbability]
  constructor
  · intro h
    exact (radialEntropyExponent_eq_attractor_iff M R).mp (Real.exp_injective h)
  · intro h
    exact congrArg Real.exp ((radialEntropyExponent_eq_attractor_iff M R).mpr h)

/-- **OVV Eq. (3.9) at the saddle.** The peak probability is
`exp (π M²/4)`, the semiclassical entropy exponential used by the paper. -/
@[zil_level bridge_theorem]
lemma radialHartleHawkingProbability_attractor (M : ℝ) :
    radialHartleHawkingProbability M (M / 2) = Real.exp (Real.pi * M ^ 2 / 4) := by
  unfold radialHartleHawkingProbability radialEntropyExponent
  congr 1
  ring

/-- The OSV flux-polarized wavefunction of OVV Eq. (6.8), with
`X = p + i φ/π`. -/
def osvFluxWave (q p : ℝ) (ψtop : ℂ → ℂ) (phi : ℝ) : ℂ :=
  (Real.exp (-(q * phi) / 2) : ℂ) *
    ψtop ((p : ℂ) + Complex.I * ((phi / Real.pi : ℝ) : ℂ))

/-- The topological-string wavefunction prescription `ψtop = exp Ftop` of OVV
Eq. (6.7). The free energy itself remains supplied data. -/
def topologicalStringWaveFunction (Ftop : ℂ → ℂ) (X : ℂ) : ℂ :=
  Complex.exp (Ftop X)

/-- Substituting `ψtop = exp Ftop` gives the exponential form of the flux wave. -/
@[zil_level bridge_theorem]
lemma osvFluxWave_eq_exp_topologicalFreeEnergy (q p phi : ℝ) (Ftop : ℂ → ℂ) :
    osvFluxWave q p (topologicalStringWaveFunction Ftop) phi =
      Complex.exp ((-(q * phi) / 2 : ℝ) +
        Ftop ((p : ℂ) + Complex.I * ((phi / Real.pi : ℝ) : ℂ))) := by
  unfold osvFluxWave topologicalStringWaveFunction
  rw [Complex.ofReal_exp, ← Complex.exp_add]

/-- The OSV Laplace integrand `exp (−qφ) |ψtop(p+iφ/π)|²`. -/
def osvIntegrand (q p : ℝ) (ψtop : ℂ → ℂ) (phi : ℝ) : ℝ :=
  Real.exp (-(q * phi)) *
    Complex.normSq (ψtop ((p : ℂ) + Complex.I * ((phi / Real.pi : ℝ) : ℂ)))

/-- Pointwise OSV identity: the Laplace integrand is the squared norm of the
flux-polarized wavefunction. -/
@[zil_level bridge_theorem]
lemma normSq_osvFluxWave (q p : ℝ) (ψtop : ℂ → ℂ) (phi : ℝ) :
    Complex.normSq (osvFluxWave q p ψtop phi) = osvIntegrand q p ψtop phi := by
  unfold osvFluxWave osvIntegrand
  rw [Complex.normSq_mul]
  rw [Complex.normSq_ofReal, ← Real.exp_add]
  congr 1
  ring_nf

/-- The formal OSV Laplace integral. Without an integrability hypothesis Lean's
totalized integral is still defined; this name therefore does not assert equality
with a microscopic BPS index. -/
def osvIndexIntegral (q p : ℝ) (ψtop : ℂ → ℂ) : ℝ :=
  ∫ phi : ℝ, osvIntegrand q p ψtop phi

/-- **OVV Eq. (6.8), norm-square form.** The formal OSV Laplace integral is the
integral of the exact flux-wave norm square. -/
@[zil_level bridge_theorem]
lemma osvIndexIntegral_eq_fluxWave_normSq (q p : ℝ) (ψtop : ℂ → ℂ) :
    osvIndexIntegral q p ψtop =
      ∫ phi : ℝ, Complex.normSq (osvFluxWave q p ψtop phi) := by
  unfold osvIndexIntegral
  apply integral_congr_ae
  filter_upwards [] with phi
  exact (normSq_osvFluxWave q p ψtop phi).symm

/-- The OSV entropy Legendre carrier `S(p,q,φ) = F(p,φ) + qφ` of Eq. (6.3),
with magnetic data held implicit in `freeEnergy`. -/
def osvBlackHoleEntropy (freeEnergy : ℝ → ℝ) (q : ℝ) : ℝ → ℝ :=
  freeEnergy + fun phi => q * phi

/-- **OSV attractor stationarity.** If `q = −∂φF`, then the Legendre entropy
has zero derivative at the attractor, formalizing Eqs. (6.3–6.4). -/
@[zil_level bridge_theorem]
lemma hasDerivAt_osvBlackHoleEntropy_of_attractor
    (freeEnergy : ℝ → ℝ) (q phi : ℝ)
    (hattr : HasDerivAt freeEnergy (-q) phi) :
    HasDerivAt (osvBlackHoleEntropy freeEnergy q) 0 phi := by
  unfold osvBlackHoleEntropy
  simpa only [id_eq, mul_one, neg_add_cancel] using
    hattr.add ((hasDerivAt_id phi).const_mul q)

/-! ### Holomorphic polarization and the supersymmetric constraint -/

/-- The holomorphic flux wave `exp (−iπW/2)` appearing in OVV Eq. (5.6),
after the paper's analytic-continuation convention. -/
def holomorphicFluxWave (W : ℂ) : ℂ :=
  Complex.exp (-Complex.I * (Real.pi : ℂ) / 2 * W)

/-- The holomorphic flux wave has probability `exp (π Im W)`. -/
lemma holomorphicFluxWave_normSq (W : ℂ) :
    Complex.normSq (holomorphicFluxWave W) = Real.exp (Real.pi * W.im) := by
  rw [holomorphicFluxWave, Complex.normSq_eq_norm_sq, Complex.norm_exp]
  simp only [pow_two, ← Real.exp_add]
  congr 1
  simp
  ring

/-- **OVV holomorphic/real polarization agreement.** The holomorphic Eq. (5.6)
wave and the real-polarization flux insertion used in Eqs. (3.8) and (6.8) have
exactly the same norm square. This is probability-level equivalence, not equality
of the two wavefunctions. -/
@[zil_level bridge_theorem]
lemma holomorphicFluxWave_normSq_eq_realPolarization (W : ℂ) :
    Complex.normSq (holomorphicFluxWave W) = Complex.normSq (fluxInsertion W) := by
  rw [holomorphicFluxWave_normSq, fluxInsertion_normSq]

/-- A supersymmetric mini-superspace carrier with a supercharge `Q` whose square
is the Wheeler–DeWitt Hamiltonian `H`. This exposes rather than hides the paper's
structural premise `Q² = H`. -/
structure SupersymmetricWheelerDeWittData (State : Type*)
    [AddCommMonoid State] [Module ℂ State] where
  Q : State →ₗ[ℂ] State
  H : State →ₗ[ℂ] State
  square : Q.comp Q = H

/-- **BPS implies Wheeler–DeWitt.** For a supplied supersymmetric carrier
`Q² = H`, every BPS state annihilated by `Q` is annihilated by `H`. This is the
exact algebraic implication used in OVV §5.1; construction of the physical
string-theory supercharge remains separate. -/
@[zil_level bridge_theorem]
lemma SupersymmetricWheelerDeWittData.bps_implies_wheelerDeWitt
    {State : Type*} [AddCommMonoid State] [Module ℂ State]
    (D : SupersymmetricWheelerDeWittData State) (psi : State)
    (hBPS : D.Q psi = 0) : D.H psi = 0 := by
  rw [← D.square]
  simp [LinearMap.comp_apply, hBPS]

/-- Multiplication by the repository's scalar mini-superspace Hamiltonian value,
bundled as a complex-linear endomorphism. -/
def scalarWheelerDeWittHamiltonian (HR HI : ℝ) : ℂ →ₗ[ℂ] ℂ :=
  LinearMap.mulLeft ℂ (complexHamiltonianConstraint HR HI)

/-- **Concrete OVV BPS-to-WDW bridge.** If a complex-linear scalar supercharge
squares to multiplication by the repository's actual complex mini-superspace
Hamiltonian `H_R − iH_I`, then every state in its BPS kernel satisfies the
existing `WheelerDeWitt HR HI` predicate. -/
@[zil_level bridge_theorem]
lemma bps_implies_scalarWheelerDeWitt (Q : ℂ →ₗ[ℂ] ℂ) (HR HI : ℝ) (psi : ℂ)
    (hsquare : Q.comp Q = scalarWheelerDeWittHamiltonian HR HI)
    (hBPS : Q psi = 0) : WheelerDeWitt HR HI psi := by
  let D : SupersymmetricWheelerDeWittData ℂ :=
    ⟨Q, scalarWheelerDeWittHamiltonian HR HI, hsquare⟩
  have h := D.bps_implies_wheelerDeWitt psi hBPS
  simpa [D, scalarWheelerDeWittHamiltonian, LinearMap.mulLeft_apply,
    WheelerDeWitt] using h

/-! ### The full finite OSV flux family -/

/-- The finite electric-potential pairing `q·φ` used by the multi-charge OSV
Laplace transform. -/
def fluxPairing {n : ℕ} (q phi : Fin n → ℝ) : ℝ := ∑ i, q i * phi i

/-- The genuine finite multi-flux version of the OVV Eq. (6.8) wavefunction. -/
def osvFluxWaveFinite {n : ℕ} (q p : Fin n → ℝ)
    (psiTop : (Fin n → ℂ) → ℂ) (phi : Fin n → ℝ) : ℂ :=
  (Real.exp (-(fluxPairing q phi) / 2) : ℂ) *
    psiTop (fun i => (p i : ℂ) + Complex.I * ((phi i / Real.pi : ℝ) : ℂ))

/-- The multi-charge OSV Laplace integrand. -/
def osvIntegrandFinite {n : ℕ} (q p : Fin n → ℝ)
    (psiTop : (Fin n → ℂ) → ℂ) (phi : Fin n → ℝ) : ℝ :=
  Real.exp (-(fluxPairing q phi)) *
    Complex.normSq
      (psiTop (fun i => (p i : ℂ) + Complex.I * ((phi i / Real.pi : ℝ) : ℂ)))

/-- Pointwise multi-charge OSV identity: the full finite-dimensional Laplace
integrand is the norm square of the flux-polarized wavefunction. -/
@[zil_level bridge_theorem]
lemma normSq_osvFluxWaveFinite {n : ℕ} (q p : Fin n → ℝ)
    (psiTop : (Fin n → ℂ) → ℂ) (phi : Fin n → ℝ) :
    Complex.normSq (osvFluxWaveFinite q p psiTop phi) =
      osvIntegrandFinite q p psiTop phi := by
  unfold osvFluxWaveFinite osvIntegrandFinite
  rw [Complex.normSq_mul, Complex.normSq_ofReal, ← Real.exp_add]
  congr 1
  ring_nf

/-- The formal finite-dimensional OSV Laplace integral. As with the scalar API,
this is totalized and does not assert integrability or microscopic-index equality. -/
def osvIndexIntegralFinite {n : ℕ} (q p : Fin n → ℝ)
    (psiTop : (Fin n → ℂ) → ℂ) : ℝ :=
  ∫ phi : Fin n → ℝ, osvIntegrandFinite q p psiTop phi

/-- **Full finite-dimensional OVV Eq. (6.8).** The multi-charge OSV integral is
the integral of the exact multi-flux wavefunction norm square. -/
@[zil_level bridge_theorem]
lemma osvIndexIntegralFinite_eq_fluxWave_normSq {n : ℕ} (q p : Fin n → ℝ)
    (psiTop : (Fin n → ℂ) → ℂ) :
    osvIndexIntegralFinite q p psiTop =
      ∫ phi : Fin n → ℝ, Complex.normSq (osvFluxWaveFinite q p psiTop phi) := by
  unfold osvIndexIntegralFinite
  apply integral_congr_ae
  filter_upwards [] with phi
  exact (normSq_osvFluxWaveFinite q p psiTop phi).symm

/-- The full finite OSV wave at `n = 1` is exactly the existing scalar carrier,
so the generalization introduces no parallel semantics. -/
@[zil_level bridge_theorem]
lemma osvFluxWaveFinite_one_eq (q p phi : ℝ) (psiTop : ℂ → ℂ) :
    osvFluxWaveFinite (![q]) (![p]) (fun X => psiTop (X 0)) (![phi]) =
      osvFluxWave q p psiTop phi := by
  simp [osvFluxWaveFinite, osvFluxWave, fluxPairing]

end Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.WheelerDeWittComplexEinstein

end

/- ZIL-BEGIN -/

open Zil
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.WheelerDeWittComplexEinstein

zil attach fluxSuperpotential_add where
  formalizes @ "claim:ooguri-vafa-verlinde-finite-flux-superpotential-is-additive-under-electric-and-magnetic-flux-composition",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:ooguri-vafa-verlinde-2005-equation-2-9",
  caveat @ "claim:finite-supplied-period-carrier-not-a-construction-of-calabi-yau-third-cohomology-periods-or-integral-flux-quantization"

zil attach fluxInsertion_add where
  formalizes @ "claim:additive-ovv-flux-superpotentials-give-multiplicative-real-polarization-wavefunction-insertions",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:ooguri-vafa-verlinde-2005-equations-3-8-and-2-9"

zil attach fluxInsertion_eq_lorentzianKernel where
  formalizes @ "claim:the-ovv-real-polarization-flux-insertion-is-the-existing-complex-action-kernel-with-zero-real-action-and-imaginary-action-minus-pi-over-two-times-imaginary-superpotential",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QFT.PathIntegral.lorentzianKernel",
  caveat @ "claim:negative-imaginary-action-enhancement-not-positive-imaginary-action-dissipation-or-a-cptp-contraction"

zil attach fluxSectorWeight_add where
  formalizes @ "claim:composition-of-finite-ovv-flux-data-is-represented-by-multiplication-of-the-corresponding-flux-sector-weights",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.WheelerDeWittComplexEinstein.fluxSuperpotential_add"

zil attach hartleHawkingFluxState_normSq where
  formalizes @ "claim:the-kahler-prefactored-semiclassical-hartle-hawking-flux-state-has-ovv-equation-3-8-probability-exp-minus-pi-k-over-four-plus-pi-im-w",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "paper:ooguri-vafa-verlinde-2005-equation-3-8",
  caveat @ "claim:exact-norm-square-of-the-paper-supplied-semiclassical-state-ansatz-not-a-derivation-of-the-wavefunction-from-the-full-wheeler-dewitt-theory"

zil attach radialEntropyExponent_eq_attractor_iff where
  formalizes @ "claim:the-ovv-radial-entropy-exponent-minus-pi-times-r-squared-minus-m-r-has-a-unique-attractor-radius-r-equals-m-over-two",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "paper:ooguri-vafa-verlinde-2005-equation-3-9",
  caveat @ "claim:unique-maximum-of-the-supplied-semiclassical-radial-exponent-not-a-lorentzian-cosmological-stability-or-existence-theorem"

zil attach radialHartleHawkingProbability_eq_attractor_iff where
  formalizes @ "claim:the-ovv-radial-hartle-hawking-probability-attains-its-extremal-value-if-and-only-if-r-equals-m-over-two",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.WheelerDeWittComplexEinstein.radialEntropyExponent_eq_attractor_iff"

zil attach radialHartleHawkingProbability_attractor where
  formalizes @ "claim:at-the-unique-ovv-radial-saddle-the-semiclassical-probability-is-exp-pi-m-squared-over-four-the-entropy-exponential",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "paper:ooguri-vafa-verlinde-2005-equation-3-9",
  caveat @ "claim:evaluation-of-the-supplied-radial-saddle-not-an-independent-derivation-of-microscopic-black-hole-entropy"

zil attach osvFluxWave_eq_exp_topologicalFreeEnergy where
  formalizes @ "claim:substituting-psi-top-equals-exp-f-top-into-the-ovv-flux-polarized-wavefunction-gives-the-exponential-free-energy-form",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:ooguri-vafa-verlinde-2005-equations-6-7-and-6-8",
  caveat @ "claim:the-topological-free-energy-is-supplied-data-not-a-construction-or-convergence-proof-of-the-all-genus-topological-string-partition-function"

zil attach normSq_osvFluxWave where
  formalizes @ "claim:the-osv-laplace-integrand-exp-minus-q-phi-times-psi-top-norm-square-is-pointwise-the-norm-square-of-the-flux-polarized-wavefunction",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:ooguri-vafa-verlinde-2005-equations-6-5-through-6-8"

zil attach osvIndexIntegral_eq_fluxWave_normSq where
  formalizes @ "claim:the-formal-osv-laplace-integral-is-the-integral-of-the-flux-polarized-wavefunction-norm-square",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:ooguri-vafa-verlinde-2005-equation-6-8",
  caveat @ "claim:equality-of-two-integral-presentations-after-a-pointwise-identity-not-a-proof-that-the-integral-converges-or-equals-the-microscopic-bps-witten-index"

zil attach hasDerivAt_osvBlackHoleEntropy_of_attractor where
  formalizes @ "claim:the-osv-attractor-equation-q-equals-minus-partial-phi-free-energy-makes-the-black-hole-entropy-legendre-transform-stationary",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:ooguri-vafa-verlinde-2005-equations-6-3-and-6-4",
  caveat @ "claim:stationarity-from-the-supplied-attractor-derivative-not-existence-uniqueness-or-global-maximality-of-a-physical-attractor"

zil attach holomorphicFluxWave_normSq_eq_realPolarization where
  formalizes @ "claim:the-ovv-holomorphic-flux-wave-exp-minus-i-pi-w-over-two-and-the-real-polarization-insertion-have-identical-probability-density",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:ooguri-vafa-verlinde-2005-equations-3-8-5-6-and-5-9",
  caveat @ "claim:norm-square-equivalence-of-two-semiclassical-polarizations-not-equality-of-wavefunctions-or-a-construction-of-the-geometric-quantization-transform"

zil attach SupersymmetricWheelerDeWittData.bps_implies_wheelerDeWitt where
  formalizes @ "claim:for-a-supersymmetric-mini-superspace-carrier-with-q-squared-equal-h-every-bps-state-q-psi-zero-is-a-wheeler-dewitt-state-h-psi-zero",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "paper:ooguri-vafa-verlinde-2005-section-5-1",
  caveat @ "claim:exact-algebraic-implication-from-a-bundled-q-squared-equals-h-certificate-not-a-construction-of-the-physical-string-supercharge-or-proof-that-mini-superspace-is-exact-beyond-the-bps-sector"

zil attach bps_implies_scalarWheelerDeWitt where
  formalizes @ "claim:when-the-bps-supercharge-squares-to-the-repository-complex-scalar-hamiltonian-h-r-minus-i-h-i-its-kernel-satisfies-the-existing-wheeler-dewitt-predicate",
  epistemic_status @ "ansatz-loaded",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.WheelerDeWittLusanna.WheelerDeWitt",
  supported_by @ "paper:ooguri-vafa-verlinde-2005-section-5-1",
  caveat @ "claim:concrete-identification-with-the-existing-scalar-minisuperspace-equation-conditional-on-the-explicit-q-squared-equals-h-certificate"

zil attach normSq_osvFluxWaveFinite where
  formalizes @ "claim:for-arbitrary-finitely-many-electric-and-magnetic-flux-components-the-full-osv-laplace-integrand-is-pointwise-the-norm-square-of-the-flux-polarized-wavefunction",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:ooguri-vafa-verlinde-2005-equations-6-5-through-6-8"

zil attach osvIndexIntegralFinite_eq_fluxWave_normSq where
  formalizes @ "claim:the-full-finite-multi-charge-osv-laplace-integral-is-the-integral-of-the-multi-flux-wavefunction-norm-square",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:ooguri-vafa-verlinde-2005-equation-6-8",
  caveat @ "claim:finite-dimensional-totalized-integral-representation-not-integrability-regulator-independence-or-microscopic-bps-index-equality"

zil attach osvFluxWaveFinite_one_eq where
  formalizes @ "claim:the-full-finite-osv-flux-wave-specializes-at-one-charge-component-to-the-existing-scalar-osv-carrier",
  epistemic_status @ "consistency-identity",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.WheelerDeWittComplexEinstein.osvFluxWave"

zil_file_contract physlib.wheelerDeWittOoguriVafaVerlinde where
  promises "A finite and kernel-checked carrier for the Ooguri-Vafa-Verlinde 2005 flux Hartle-Hawking and OSV algebra: symplectic flux superpotentials compose additively, real-polarization insertions compose multiplicatively and reuse the repository complex-action kernel, the holomorphic and real polarizations have identical probability density, the full Kahler-prefactored semiclassical state has the equation 3.8 norm square, the equation 3.9 radial probability has the unique saddle R equals M over two and peak exp pi M squared over four, the OSV flux wave has exactly the Laplace integrand as its norm square both for the scalar API and the paper's arbitrary finite flux family, the one-component multi-flux wave reduces exactly to the scalar carrier, the attractor derivative makes the entropy Legendre transform stationary, and a bundled supersymmetry certificate Q squared equals H proves that every BPS state is a Wheeler-DeWitt state."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects [
    "lean:Physlib.QFT.PathIntegral.lorentzianKernel",
    "lean:Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.WheelerDeWittLusanna.WheelerDeWitt"
  ]
  forbids_substitutes [
    "presenting supplied finite periods as a construction of Calabi-Yau cohomology or flux quantization",
    "presenting the supplied topological wavefunction as a proved all-genus topological-string partition function",
    "presenting the formal OSV integral identity as a proof of convergence or equality to the microscopic BPS Witten index",
    "presenting the Euclidean radial saddle as Lorentzian cosmological evolution",
    "presenting the negative-imaginary-action flux enhancement as dissipative contraction",
    "presenting the abstract Q-squared-equals-H carrier as a construction of the physical string-theory supercharge"
  ]
  witnessed_by [
    fluxSuperpotential_add,
    fluxInsertion_add,
    fluxInsertion_eq_lorentzianKernel,
    fluxSectorWeight_add,
    hartleHawkingFluxState_normSq,
    radialEntropyExponent_eq_attractor_iff,
    radialHartleHawkingProbability_eq_attractor_iff,
    radialHartleHawkingProbability_attractor,
    osvFluxWave_eq_exp_topologicalFreeEnergy,
    normSq_osvFluxWave,
    osvIndexIntegral_eq_fluxWave_normSq,
    hasDerivAt_osvBlackHoleEntropy_of_attractor,
    holomorphicFluxWave_normSq_eq_realPolarization,
    SupersymmetricWheelerDeWittData.bps_implies_wheelerDeWitt,
    bps_implies_scalarWheelerDeWitt,
    normSq_osvFluxWaveFinite,
    osvIndexIntegralFinite_eq_fluxWave_normSq,
    osvFluxWaveFinite_one_eq
  ]

/- ZIL-END -/

#zil_formalization_lint physlib.wheelerDeWittOoguriVafaVerlinde

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.NewtonGScreen.CouplingCore
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementScreenArea
public import Physlib.QuantumMechanics.ComplexAction.NewtonGScreen.MuonAnomalyCore

/-!
# The screen-coupling product G·α in BCJ color-kinematics form

The BCJ double copy (`BCJDoubleCopy.ColorKinematicsDoubleCopy`) organizes an amplitude into
channels, each pairing a **color factor** `cᵢ` (from the gauge structure constants) with a
**kinematic numerator** `nᵢ`. The gauge amplitude is `A = Σ cᵢnᵢ/Dᵢ`; the **double copy** strips
the color and inserts a second kinematic copy, `M = Σ nᵢñᵢ/Dᵢ` (the double copy).

The one-region entanglement screen (`ComptonClock.EntanglementScreenArea`, §C) isolates the two
fundamental couplings from a single numerator `X = (e/m)²·(log K)²`:

  `α = X/(ε₀·G·N)`   (`fineStructure_from_screenBits`),
  `G = X/(ε₀·α·N)`   (`newtonG_from_screenBits`),

with `N` the holographic bit count of the screen. This module reads that numerator through the BCJ
grammar. The two square factors of `X` are exactly a color factor and a kinematic numerator:

  `c = e/m`      the charge-to-mass ratio (electromagnetism supplies the **color** factor — `α`
                 measures `e` against the Planck charge),
  `n = log K`    the entanglement entropy in nats (gravity supplies the **kinematic** numerator —
                 the entropic route to Newton's `G`).

* **§A** builds `screenBCJ`, a `BCJColorKinematicsDuality` with color factors `±e/m` and kinematic
  numerators `±log K` (both Jacobi identities hold trivially), and exposes its `s`-channel data.
* **§B** factorizes the shared screen numerator as the color-square times the kinematic-square,
  `X = c_s²·n_s²`, and identifies it with the square of the gauge single-copy numerator
  `(c_s·n_s)²` — the double copy at the level of the numerator.
* **§C** the product identity `G·α = (c_s·n_s)²/(ε₀·N)`: the product equals the squared gauge
  numerator over `ε₀·N`, and `α`, `G` are the two ways of solving the one relation for one coupling
  given the other.

These are exact consistency identities: `N` depends on `G`, so the product `G·α` is a closed-form
expression in the screen data. On the screen the two couplings are the color-single and
kinematic-double reads of the same numerator.

## References

* Z. Bern, J. J. M. Carrasco, H. Johansson, *New Relations for Gauge-Theory Amplitudes*,
  Phys. Rev. D **78** (2008) 085011, arXiv:0805.3993 — color–kinematics duality and the double copy.
* J. D. Bekenstein, *Black holes and entropy*, Phys. Rev. D **7** (1973) 2333; S. W. Hawking,
  *Particle creation by black holes*, Commun. Math. Phys. **43** (1975) 199 — the horizon entropy
  `S = A/4` used at holographic saturation.
* E. Verlinde, JHEP **04** (2011) 029 — the screen bit count; K. Nagao, H. B. Nielsen, Prog. Theor.
  Phys. **126** (2011) 1021, arXiv:1104.3381 — the complex-action framework.
* Repo dictionary: `ComptonClock.EntanglementScreenArea` §C (`fineStructure_from_screenBits`,
  `newtonG_from_screenBits`) and §B (`entanglementScreen_holographicBits`).
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.GravitationalElectromagneticScreenDoubleCopy

open Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementScreenArea
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntropicProperDistance
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolic
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchwingerRapidityEquation
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalyRapidity
open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.AnomalousMagneticMoment
open Physlib.Thermodynamics

/-! ## A. the screen's color and kinematic data -/

/-- The **screen color factor** `c = e/m`: the particle's charge-to-mass ratio. In the BCJ grammar
this is the gauge/color datum — the fine-structure constant `α = e²/(4πε₀ℏc)` measures the charge
`e` (hence `c`) against the Planck charge. -/
noncomputable def screenColorFactor (e m : ℝ) : ℝ := e / m

/-- The **screen kinematic numerator** `n = log K`: the one-region entanglement entropy in nats
(`K = coth η` the Schmidt number). In the BCJ grammar this is the kinematic datum — the gravity
sector's numerator, set by the entanglement entropy; it is the factor whose square gives the
screen its area (`entanglementScreenArea`) and its bit count. -/
noncomputable def screenKinematicNumerator (η : ℝ) : ℝ := Real.log (schmidtNumber η)

/-- **The screen BCJ color–kinematics duality.** A three-channel `(s,t,u)` duality whose color
factors are the charge-to-mass ratio `±e/m` and whose kinematic numerators are the entanglement
nats `±log K`; both satisfy the Jacobi identities `c_s+c_t+c_u = 0`, `n_s+n_t+n_u = 0`. The
`s`-channel pairs charge (color) with entanglement (kinematic): `c_s = e/m`, `n_s = log K`. -/
noncomputable def screenBCJ (e m η : ℝ) : BCJColorKinematicsDuality where
  c_s := screenColorFactor e m
  c_t := -screenColorFactor e m
  c_u := 0
  n_s := screenKinematicNumerator η
  n_t := -screenKinematicNumerator η
  n_u := 0
  color_jacobi := by ring
  kinematic_jacobi := by ring

@[simp] theorem screenBCJ_c_s (e m η : ℝ) : (screenBCJ e m η).c_s = e / m := rfl

@[simp] theorem screenBCJ_n_s (e m η : ℝ) :
    (screenBCJ e m η).n_s = Real.log (schmidtNumber η) := rfl

/-! ## B. the screen numerator is the color-square × kinematic-square -/

/-- **The shared screen numerator factorizes as color² × kinematic².** The numerator
`X = (e/m)²·(log K)²` common to both coupling identities (`fineStructure_from_screenBits`,
`newtonG_from_screenBits`) is the product of the squared color factor `(e/m)²` (charge) and the
squared kinematic numerator `(log K)²` (entanglement) — the BCJ double-copy factorization. -/
lemma screen_numerator_colorKinematic_square (e m η : ℝ) :
    (e / m) ^ 2 * Real.log (schmidtNumber η) ^ 2
      = (screenBCJ e m η).c_s ^ 2 * (screenBCJ e m η).n_s ^ 2 := by
  simp

/-- **The gauge single-copy numerator squared is the shared screen numerator.** The gauge amplitude
pairs color with kinematics, `c_s·n_s = (e/m)·log K`; squaring it — the double copy that strips the
color and inserts a second kinematic copy — returns `(e/m)²·(log K)²`. This is the numerator
double copy. -/
lemma screen_gauge_numerator_squared (e m η : ℝ) :
    ((screenBCJ e m η).c_s * (screenBCJ e m η).n_s) ^ 2
      = (screenBCJ e m η).c_s ^ 2 * (screenBCJ e m η).n_s ^ 2 := by
  ring

/-! ## C. the coupling product is the double copy -/

/-- **The product of the gravitational and electromagnetic couplings is the screen invariant.**
`G·α = (e/m)²·(log K)²/(ε₀·N)` with `N` the holographic bit count of the one-region entanglement
screen: substituting the bit count `entanglementScreen_holographicBits` eliminates `ℏ` and `c`,
leaving the charge-to-mass ratio squared times the entanglement nats squared over `ε₀` times the bit
count. An exact consistency identity: `N` itself depends on `G`, so the product is a closed-form
expression in the screen data. -/
lemma screen_coupling_product (e eps0 m c ħ G η : ℝ)
    (heps : eps0 ≠ 0) (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) (hG : G ≠ 0) (hη : 0 < η) :
    G * fineStructure e eps0 ħ c
      = (e / m) ^ 2 * Real.log (schmidtNumber η) ^ 2
        / (eps0 * holographicBits (sphereArea (entropicProperDistance m c ħ η)) G ħ c) := by
  rw [entanglementScreen_holographicBits m c ħ G η hm hc hħ hG]
  have hlog : Real.log (schmidtNumber η) ≠ 0 :=
    (Real.log_pos (schmidtNumber_gt_one η hη)).ne'
  have hπ := Real.pi_ne_zero
  unfold fineStructure
  field_simp

/-- **The screen-coupling product `G·α` in BCJ form.** The product `G·α` of Newton's constant and
the fine-structure constant equals the square of the gauge single-copy numerator
`c_s·n_s = (e/m)·log K` — charge times entanglement — over `ε₀` and the screen bit count `N`:

  `G·α = (c_s·n_s)²/(ε₀·N)`.

Electromagnetism supplies the color factor `c_s = e/m`; gravity supplies the kinematic numerator
`n_s = log K` (entanglement, the entropic route to `G`). Their BCJ product — color times kinematic,
squared, the double copy that turns a gauge amplitude into a gravitational one — is exactly the
product of the two couplings on the screen. An exact consistency identity (`N` depends on
`G`), an algebraic consequence of the screen-coupling isolations. -/
lemma screen_couplings_double_copy (e eps0 m c ħ G η : ℝ)
    (heps : eps0 ≠ 0) (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) (hG : G ≠ 0) (hη : 0 < η) :
    G * fineStructure e eps0 ħ c
      = ((screenBCJ e m η).c_s * (screenBCJ e m η).n_s) ^ 2
        / (eps0 * holographicBits (sphereArea (entropicProperDistance m c ħ η)) G ħ c) := by
  rw [screen_coupling_product e eps0 m c ħ G η heps hm hc hħ hG hη, screenBCJ_c_s, screenBCJ_n_s]
  ring

/-- **`α` and `G` are the two ways of solving one screen relation.**
Both couplings equal the same color-kinematics product `c_s²·n_s² = (e/m)²·(log K)²` divided by
`ε₀`, the screen bit count `N`, and the *other* coupling:

  `α = c_s²n_s²/(ε₀·G·N)`   and   `G = c_s²n_s²/(ε₀·α·N)`.

On the screen each coupling is the same relation solved for the opposite coupling. Restates the
isolations `fineStructure_from_screenBits` and `newtonG_from_screenBits` in the BCJ grammar. -/
lemma screen_couplings_conjugate_reads (e eps0 m c ħ G η : ℝ)
    (heps : eps0 ≠ 0) (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) (hG : G ≠ 0) (hη : 0 < η)
    (he : e ≠ 0) :
    fineStructure e eps0 ħ c
        = (screenBCJ e m η).c_s ^ 2 * (screenBCJ e m η).n_s ^ 2
          / (eps0 * G * holographicBits (sphereArea (entropicProperDistance m c ħ η)) G ħ c)
    ∧ G = (screenBCJ e m η).c_s ^ 2 * (screenBCJ e m η).n_s ^ 2
          / (eps0 * fineStructure e eps0 ħ c
              * holographicBits (sphereArea (entropicProperDistance m c ħ η)) G ħ c) := by
  rw [screenBCJ_c_s, screenBCJ_n_s]
  exact ⟨fineStructure_from_screenBits e eps0 m c ħ G η heps hm hc hħ hG hη,
    newtonG_from_screenBits e eps0 m c ħ G η heps hm hc hħ hG hη he⟩

/-! ## D. solving the coupling system

The two conjugate reads of §C are one equation (rank one): each is the other solved for the
opposite coupling, so together they fix the product `G·α` (`screen_reads_equivalent`). Determining a
single coupling needs one more, independent equation. Closing the system with the definition of `α`
and the bit count `N` as an independent input isolates Newton's constant with `α` and the charge
eliminated (`newtonG_from_screen_system`). -/

/-- **The screen system has rank one.** For nonzero `ε₀`, `N`, `G`, `α`, the read `G = X/(ε₀αN)`
holds iff the read `α = X/(ε₀GN)` holds — algebraically the same statement, each the other solved
for the opposite coupling. The two conjugate reads are therefore a single constraint, fixing the
product `G·α`. -/
lemma screen_reads_equivalent (X eps0 N G α : ℝ)
    (heps : eps0 ≠ 0) (hN : N ≠ 0) (hG : G ≠ 0) (hα : α ≠ 0) :
    G = X / (eps0 * α * N) ↔ α = X / (eps0 * G * N) := by
  rw [eq_div_iff (mul_ne_zero (mul_ne_zero heps hα) hN),
      eq_div_iff (mul_ne_zero (mul_ne_zero heps hG) hN)]
  constructor <;> intro h <;> linear_combination h

/-- **Each read is the product law.** `G = X/(ε₀αN)` is equivalent to `G·α = X/(ε₀N)`: the single
constraint the screen system imposes is exactly the product law of `screen_couplings_double_copy`.
-/
lemma screen_read_iff_product (X eps0 N G α : ℝ)
    (heps : eps0 ≠ 0) (hN : N ≠ 0) (hα : α ≠ 0) :
    G = X / (eps0 * α * N) ↔ G * α = X / (eps0 * N) := by
  rw [eq_div_iff (mul_ne_zero (mul_ne_zero heps hα) hN),
      eq_div_iff (mul_ne_zero heps hN)]
  constructor <;> intro h <;> linear_combination h

/-- **Closing the system isolates `G`, eliminating both `α` and the charge.** Feed the double-copy
product law `G·α = (e/m)²(log K)²/(ε₀·N)` with the bit count `N` taken as an *independent* input,
together with the definition `α = e²/(4πε₀ℏc)`. The elementary charge `e` and the permittivity `ε₀`
cancel and `α` is eliminated, leaving Newton's constant in terms of `ℏ`, `c`, the mass, the
entanglement nats and the count alone:

  `G = 4π·ℏc·(log K)²/(m²·N)`.

This is the Verlinde/area-per-bit form (`Thermodynamics.NewtonGIsolation.newtonG_eq_area_per_bit`):
an `N` fixed independently of `G` turns the rank-one identity into a determination of `G`. Reading
`N` instead as `A/ℓ_P²` (with `ℓ_P² = Gℏ/c³`) reinserts `G`, which is why `N` here is kept as an
independent input. -/
lemma newtonG_from_screen_system (e eps0 m c ħ G η N : ℝ)
    (heps : eps0 ≠ 0) (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) (he : e ≠ 0) (hN : N ≠ 0)
    (hprod : G * fineStructure e eps0 ħ c
              = (e / m) ^ 2 * Real.log (schmidtNumber η) ^ 2 / (eps0 * N)) :
    G = 4 * Real.pi * ħ * c * Real.log (schmidtNumber η) ^ 2 / (m ^ 2 * N) := by
  have hπ := Real.pi_ne_zero
  have hαval : fineStructure e eps0 ħ c = e ^ 2 / (4 * Real.pi * eps0 * ħ * c) := rfl
  have hαne : fineStructure e eps0 ħ c ≠ 0 := by
    rw [hαval]
    exact div_ne_zero (pow_ne_zero 2 he)
      (by exact mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hπ) heps) hħ) hc)
  have hG_eq : G = (e / m) ^ 2 * Real.log (schmidtNumber η) ^ 2 / (eps0 * N)
      / fineStructure e eps0 ħ c := by
    rw [eq_div_iff hαne]; exact hprod
  rw [hG_eq, hαval]
  field_simp

/-! ## E. the `G`-free closure: holographic saturation, and its Planck-scale fixed point

§D's solve becomes a determination of `G` once `N` is fixed without the Planck area. The repo
supplies such an `N` by **holographic saturation.** The Bekenstein–Hawking/Ryu–Takayanagi entropy of
the screen is a quarter of its bit count, `S_BH = N/4`
(`AdSCFT.RyuTakayanagiFormulaAlgebra.rtAreaEntropy = area/(4G)`); the one-region pair puts
entanglement entropy `S_EE = log K` on it (`K = coth η` the Schmidt number, the Bell value `K = 2`).
Content equal to capacity fixes

  `N = 4·log K`      (a `K`-number of `SchmidtRapidityHyperbolic`; `G`-free),

closing §D's solve into the dimensionless statement `α_G = G·m²/(ℏc) = π·log K`, equivalently
`G = π·ℏc·log K/m²`.

The well-posed content is dimensionless: `α_G = π·log K`, with `α_G = G·m²/(ℏc)` the gravitational
coupling (`α_G ∝ G`, so measuring it measures `G`). The saturation condition reads
`m² = π·log K·m_P²` (`holographic_saturation_mass_planckScale`), `m_P² = ℏc/G`: the screen at its
bound is the Planck-scale one, where `α_G` is `O(1)`. The framework's dimensionless outputs — e.g.
`α = 2π(K²−1)` of the muon-anomaly arc — carry its `G`-free content. -/

/-- **The entanglement closure `N = 4·log K` (holographic saturation) determines `G`.** Feeding the
`α`-eliminated solve of `newtonG_from_screen_system` with the screen at its holographic bound —
`N = 4·log K`, the Bekenstein–Hawking entropy `N/4` set equal to the pair's entanglement entropy
`log K` — cancels one power of `log K` and gives a `G`-free relation from `ℏ`, `c`, the mass, and
the Schmidt `K`-number alone (dimensionlessly, `α_G = π·log K`):

  `G = π·ℏc·log K/m²`. -/
lemma newtonG_at_holographic_saturation (m c ħ G η N : ℝ)
    (hm : m ≠ 0) (hlogK : Real.log (schmidtNumber η) ≠ 0)
    (hsol : G = 4 * Real.pi * ħ * c * Real.log (schmidtNumber η) ^ 2 / (m ^ 2 * N))
    (hsat : N = 4 * Real.log (schmidtNumber η)) :
    G = Real.pi * ħ * c * Real.log (schmidtNumber η) / m ^ 2 := by
  subst hsat
  rw [hsol]
  field_simp

/-- **The holographic-saturation closure is the Planck-mass condition.** The entanglement-closed
`G = π·ℏc·log K/m²` is equivalent to `m² = π·log K·m_P²` with `m_P² = ℏc/G` (`planckMassSq`) the
squared Planck mass: the screen actually at its holographic bound is the Planck-scale one. Read
dimensionlessly this is `α_G = G·m²/(ℏc) = π·log K` — an `O(1)` gravitational coupling, as befits
`m ∼ m_P`. For a lighter particle `α_G = π·log K·(m/m_P)² ≪ 1` is the weakness of gravity, and its
ratio to the saturated value is `α_G⁻¹ = (m_P/m)²/(π log K)`, a `G`-built quantity. -/
lemma holographic_saturation_mass_planckScale (m c ħ G η : ℝ)
    (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) (hlogK : Real.log (schmidtNumber η) ≠ 0)
    (hsat_sol : G = Real.pi * ħ * c * Real.log (schmidtNumber η) / m ^ 2) :
    m ^ 2 = Real.pi * Real.log (schmidtNumber η) * planckMassSq G ħ c := by
  have hπ := Real.pi_ne_zero
  unfold planckMassSq
  rw [hsat_sol]
  field_simp

/-! ## F. the gravitational coupling paired with the electromagnetic sector

Read dimensionlessly, the saturation condition becomes a statement about the gravitational coupling
`α_G = G·m²/(ℏc)` that pairs with the electromagnetic sector. Two such statements follow. -/

/-- **At holographic saturation the gravitational coupling is the entanglement entropy (up to
`π`).** Reading the saturation solve `G = π·ℏc·log K/m²` through `gravitationalCoupling` gives the
dimensionless identity

  `α_G = G·m²/(ℏc) = π·log K`,

the gravitational fine-structure constant equal to `π` times the one-region entanglement entropy
`log K` (Schmidt `K = coth η`). A dimensionless relation between gravity's coupling and the
one-region entanglement entropy. -/
lemma gravitationalCoupling_at_saturation (m c ħ G η : ℝ)
    (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0)
    (hsat_sol : G = Real.pi * ħ * c * Real.log (schmidtNumber η) / m ^ 2) :
    gravitationalCoupling G m ħ c = Real.pi * Real.log (schmidtNumber η) := by
  unfold gravitationalCoupling
  rw [hsat_sol]
  field_simp

/-- **The gravitational and electromagnetic couplings, entanglement eliminated.** The Schmidt number
`K = coth η` that fixes the muon's anomalous moment through the rapidity relation `α = 2π(K²−1)`
(`MuonAnomaly.alpha_eq_twoPi_schmidt_defect`) enters the gravitational coupling as `α_G = π·log K`
(`gravitationalCoupling_at_saturation`); `K` cancels between the two sectors and the gravitational
coupling is fixed by the fine-structure constant alone:

  `α_G = (π/2)·log(1 + α/(2π))`      (leading order `α_G ≈ α/4 ≈ 0.00182`).

A `G`-free, dimensionless relation between the two couplings, with the entanglement parameter, `ℏ`
and `c` all eliminated. The shared `K` is fixed by measurement: the rapidity `η` is the muon `g−2`
storage-ring operating point — `γ = cosh η ≈ 29.3`, `p ≈ 3.094 GeV/c`, the BNL/Fermilab
configuration (`AnomalyRapidity`) — so `K = coth η` follows from the measured anomaly
`a ≈ 0.00116592`; and its entanglement entropy `log K` is the gravitational-action null-boundary
joint rapidity (`HaywardJointRapidity.haywardBoost_eq_schmidtRapidity`; Lehner–Myers–Poisson–Sorkin
arXiv:1609.00207, Hayward Phys. Rev. D 47 (1993) 3275), the *same* boost parameter as the muon's.
The identity is exact; as an `α_G` statement its numerical side is read through `G`. -/
lemma gravitational_electromagnetic_coupling_relation (α m c ħ G η : ℝ)
    (hη : 0 < η)
    (hanom : schwingerAnomaly α = rapidityAnomaly η)
    (hsat : gravitationalCoupling G m ħ c = Real.pi * Real.log (schmidtNumber η)) :
    gravitationalCoupling G m ħ c = (Real.pi / 2) * Real.log (1 + α / (2 * Real.pi)) := by
  have hπ : (2 * Real.pi) ≠ 0 := mul_ne_zero (by norm_num) Real.pi_ne_zero
  have hdef := alpha_eq_twoPi_schmidt_defect α η hη hanom
  have hK2 : 1 + α / (2 * Real.pi) = schmidtNumber η ^ 2 := by
    rw [hdef]; field_simp; ring
  rw [hsat, hK2, Real.log_pow]
  push_cast
  ring

/-! ## G. The screen identities collected -/

/-- **[The screen identities collected]** at rapidity `η` (`K = coth η` the Schmidt number), the
framework's screen identities gathered in one statement — the thermal Schmidt spectrum, the
non-Hermitian amplitude, the `G`-value formula and the `G·α` product:

* (i) `K = (1+g)/(1−g)`, `g = e^{−2η}` — the Bogdanov thermal Schmidt spectrum;
* (ii) `r_ent = r` — the entropic proper distance is the inverted Reeh–Schlieder Bell decay;
* (iii) `mc²·τ_ent = ħ·log K = S_I` — the entropic proper time is the imaginary action;
* (iv) `exp(−S_I/ℏ) = tanh η` — the non-Hermitian Schrödinger amplitude is the two-mode-squeezed
  concurrence;
* (v) `α = 2π(K²−1)` — the fine-structure constant is the Schmidt defect (muon `g−2`);
* (vi) `G = π·ħc·log K/m²` — Newton's constant at holographic saturation `N = 4·log K`;
* (vii) `G·α = (c_s·n_s)²/(ε₀·N)` — the screen-coupling product in BCJ form.

Each conjunct is an existing lemma; they share the parameter `K = coth η`. -/
lemma entropic_screen_identities (e eps0 m c ħ G η α N C₀ r : ℝ)
    (heps : eps0 ≠ 0) (hm : m ≠ 0) (hc : c ≠ 0) (hħ : ħ ≠ 0) (hG : G ≠ 0) (hη : 0 < η)
    (hC₀ : 0 < C₀) (hanom : schwingerAnomaly α = rapidityAnomaly η)
    (hconc : C₀ * Real.tanh η = C₀ * Real.exp (-(r / comptonWavelength m c ħ)))
    (hsol : G = 4 * Real.pi * ħ * c * Real.log (schmidtNumber η) ^ 2 / (m ^ 2 * N))
    (hsat : N = 4 * Real.log (schmidtNumber η)) :
    schmidtNumber η = (1 + Real.exp (-(2 * η))) / (1 - Real.exp (-(2 * η)))
    ∧ entropicProperDistance m c ħ η = r
    ∧ m * c ^ 2 * entropicProperTime m c ħ η = ħ * Real.log (schmidtNumber η)
    ∧ entropicAmplitude m c ħ η = Real.tanh η
    ∧ α = 2 * Real.pi * (schmidtNumber η ^ 2 - 1)
    ∧ G = Real.pi * ħ * c * Real.log (schmidtNumber η) / m ^ 2
    ∧ G * fineStructure e eps0 ħ c
        = ((screenBCJ e m η).c_s * (screenBCJ e m η).n_s) ^ 2
          / (eps0 * holographicBits (sphereArea (entropicProperDistance m c ħ η)) G ħ c) := by
  have hlogK : Real.log (schmidtNumber η) ≠ 0 := (Real.log_pos (schmidtNumber_gt_one η hη)).ne'
  exact ⟨schmidtNumber_eq_thermal_ratio η hη,
    entropicProperDistance_of_bellConcurrence m c ħ η C₀ r hm hc hħ hη hC₀ hconc,
    restEnergy_mul_entropicProperTime m c ħ η hm hc,
    entropicAmplitude_eq_tanh m c ħ η hm hc hħ hη,
    alpha_eq_twoPi_schmidt_defect α η hη hanom,
    newtonG_at_holographic_saturation m c ħ G η N hm hlogK hsol hsat,
    screen_couplings_double_copy e eps0 m c ħ G η heps hm hc hħ hG hη⟩

end Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.GravitationalElectromagneticScreenDoubleCopy

end

/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronWaveFunctionLink
public import Physlib.QuantumMechanics.ComplexAction.Hopf.StokesSpinorIsomorphism
public import Physlib.QuantumMechanics.ComplexAction.PenroseTwistorSpace
public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.WeylSpinorPoincareSphere
public import Physlib.QuantumMechanics.ComplexAction.PurelyNonlinearGeneralizedTrig

/-!
# Resolving the Madelung wave function: Hopf fibration, Wilson loop, twistor, Möbius

The electron wave function of `ElectronWaveFunctionLink` is encoded in the Pauli 2-spinor `χ : Fin 2 → ℂ`.
Written in Madelung polar form `ψ = R·e^{iS/ℏ}`, its three data — amplitude `R`, phase `S`, and spin
direction — are **exactly the three data of the Hopf fibration `S³ → S²`** of `χ`, and each is a facet a further
geometric structure resolves:

* **Hopf** — the amplitude is the `S³` radius `R² = ‖χ‖² = hopfIntensity χ`
 (`madelung_amplitude_is_hopfIntensity`); the **phase `e^{iS/ℏ}` is the `S¹` fiber**: a global phase moves `χ`
 along the fiber and leaves the Bloch base fixed (`madelung_phase_is_hopfFiber`,
 `Hopf.hopfBase_phase_invariant`).
* **Wilson loop** — the phase `S = ∮ p·dq` is the closed-loop action / holonomy, with `p = ∂S/∂q`
 (`madelung_phase_is_loopAction`, `generatingF`); read topologically, the Hopf fiber phase `ribbonTwist e^{2πih}`
 is the Chern–Simons Wilson-loop topological spin (`ChernSimons.hopf_ribbon_twist_is_wilson_topological_spin`).
* **Twistor** — the spinor `χ` and a Minkowski point `x` (Hermitian `2×2`) form a **null Penrose twistor**
 `Z = (i·x·χ, χ)` (`madelung_spinor_null_twistor`, `incident_isNull`), whose null direction is the `CP¹` point
 `weylRatio χ`.
* **Möbius** — that `CP¹` point `weylRatio χ = χ₀/χ₁` is the single coordinate shared by the Bloch base, the
 twistor direction, and the Riemann sphere; it is **phase-invariant** (`madelung_cp1_phaseInvariant`,
 `weylRatio_smul` — the same `S¹` fiber quotient) and transforms under `SL(2,ℂ)` by **Möbius**
 (`madelung_cp1_mobius`, `sl2c_weylRatio`).

So the Madelung wave function is *resolved*: `R²` is the Hopf/Born intensity, its phase is the `S¹` fiber = a
Wilson-loop holonomy, `(χ,x)` is a null twistor, and its direction is a `CP¹` point acted on by `SL(2,ℂ)`
Möbius — one spinor `χ`, four geometries.

* **§A — Hopf** (`madelung_amplitude_is_hopfIntensity`, `madelung_phase_is_hopfFiber`).
* **§B — Wilson loop** (`madelung_phase_is_loopAction`).
* **§C — twistor** (`madelung_spinor_null_twistor`).
* **§D — Möbius** (`madelung_cp1_phaseInvariant`, `madelung_cp1_mobius`).
* **§E — assembled** (`madelung_geometric_resolution`).

Every statement is exact reuse: `stokesS0_eq_normSq`, `hopfBase_phase_invariant`,
`momentum_eq_generatingF_deriv`, `hopf_ribbon_twist_is_wilson_topological_spin`, `incident_isNull`,
`weylRatio_smul`, `sl2c_weylRatio`. The content is the *identification* — the Madelung amplitude/phase/direction
of the electron spinor are the Hopf intensity / `S¹` fiber (= Wilson holonomy) / `CP¹` point (= twistor
direction under `SL(2,ℂ)` Möbius). No new axioms.

## References

* H. Hopf; R. Penrose (twistors); E. Witten (Chern–Simons Wilson loops). Repo dependencies:
 `Hopf.{FibrationSpinorMap,StokesSpinorIsomorphism}`, `PenroseTwistorSpace`,
 `AdSCFT.WeylSpinorPoincareSphere`, `ChernSimons.HopfAlgebraWilsonLoop`, `PurelyNonlinearGeneralizedTrig`,
 `HorizonCell.ElectronWaveFunctionLink`.

No new axioms.
-/

set_option autoImplicit false

open scoped Matrix MatrixGroups
open Physlib.QuantumMechanics.ComplexAction.Hopf.FibrationSpinorMap
open Physlib.QuantumMechanics.ComplexAction.Hopf.StokesSpinorIsomorphism
open Physlib.QuantumMechanics.ComplexAction.PenroseTwistorSpace
open Physlib.QuantumMechanics.ComplexAction.AdSCFT.WeylSpinorPoincareSphere
open Physlib.QuantumMechanics.ComplexAction.PurelyNonlinearGeneralizedTrig

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronMadelungGeometricResolution

/-! ## §A — Hopf: amplitude is the intensity, phase is the fiber -/

/-- **[The Madelung amplitude is the Hopf intensity] `R² = ‖χ‖²`.** The Born density / squared amplitude of the
electron spinor `χ` is the Hopf `S³` radius `hopfIntensity χ = χ†χ = |χ₀|² + |χ₁|²` — the amplitude datum of the
Madelung wave function is the Hopf/Stokes intensity. -/
theorem madelung_amplitude_is_hopfIntensity (χ : Fin 2 → ℂ) :
    hopfIntensity χ = ((Complex.normSq (χ 0) + Complex.normSq (χ 1) : ℝ) : ℂ) := by
  unfold hopfIntensity; exact stokesS0_eq_normSq χ

/-- **[The Madelung phase is the Hopf `S¹` fiber].** A global phase `u` (`|u| = 1`) — the Madelung phase factor
`e^{iS/ℏ}` acting on `χ` — leaves the Bloch/Stokes base `hopfBase χ` fixed: the phase moves the spinor along the
`S¹` Hopf fiber over a fixed base point. The Madelung phase *is* the Hopf fiber coordinate. -/
theorem madelung_phase_is_hopfFiber (u : ℂ) (χ : Fin 2 → ℂ) (hu : star u * u = 1) :
    hopfBase (phaseRotate u χ) = hopfBase χ :=
  hopfBase_phase_invariant u χ hu

/-! ## §B — Wilson loop: the phase is a holonomy -/

/-- **[The Madelung phase is the closed-loop action] `p = ∂S/∂q`.** The Madelung phase is the generating
function `S = generatingF p a = ∮ p dq'`, whose derivative is the momentum `p` (Hamilton–Jacobi): the phase is
the closed-loop action, the abelian Wilson-loop holonomy `∮ p·dq`. -/
theorem madelung_phase_is_loopAction (pFun : ℝ → ℝ) (hp : Continuous pFun) (a q : ℝ) :
    HasDerivAt (generatingF pFun a) (pFun q) q :=
  momentum_eq_generatingF_deriv pFun hp a q

/-! ## §C — twistor: the spinor and a point are a null twistor -/

/-- **[The Madelung spinor and a spacetime point form a null twistor].** For a Minkowski point `x` (Hermitian
`2×2`, `x^{AA'}`) the twistor `Z = (i·x·χ, χ)` is **incident** to `x` (`ω = i·x·π`, `π = χ`), hence a **null**
twistor `Σ(Z) = 0` (`incident_isNull`), lying on the light cone; and its `CP¹` null direction is the spinor
ratio `weylRatio χ`. The Madelung spinor + position is a Penrose twistor. -/
theorem madelung_spinor_null_twistor (χ : Fin 2 → ℂ) (x : Matrix (Fin 2) (Fin 2) ℂ)
    (hx : ∀ i j, x i j = (starRingEnd ℂ) (x j i)) :
    IsNullTwistor (Complex.I • (x *ᵥ χ), χ)
      ∧ twistorDirection (Complex.I • (x *ᵥ χ), χ) = weylRatio χ :=
  ⟨incident_isNull (Complex.I • (x *ᵥ χ), χ) x hx rfl, rfl⟩

/-! ## §D — Möbius: the direction is a CP¹ point under SL(2,ℂ) -/

/-- **[The Madelung `CP¹` direction is phase-invariant] `weylRatio (u·χ) = weylRatio χ`.** The spinor ratio
`χ₀/χ₁ ∈ CP¹` — the Bloch base / twistor direction — is unchanged by a global phase (or any nonzero scale): the
same `S¹` fiber quotient as the Hopf map. The Madelung phase does not move the `CP¹` point. -/
theorem madelung_cp1_phaseInvariant (u : ℂ) (hu : u ≠ 0) (χ : Fin 2 → ℂ) :
    weylRatio (u • χ) = weylRatio χ :=
  weylRatio_smul u hu χ

/-- **[`SL(2,ℂ)` acts on the Madelung `CP¹` direction by Möbius].** The `CP¹` coordinate `a/b` (`= χ₀/χ₁`)
transforms under the Lorentz double-cover `SL(2,ℂ)` by the Möbius map `(M₀₀a+M₀₁b)/(M₁₀a+M₁₁b)`: the
Riemann-sphere / boundary conformal action on the Madelung wave function's spin direction. -/
theorem madelung_cp1_mobius (M : SL(2, ℂ)) (a b : ℂ) (hb : b ≠ 0)
    (hden : (M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * a + (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1 * b ≠ 0) :
    M.toGL • ((a / b : ℂ) : OnePoint ℂ)
      = ((((M : Matrix (Fin 2) (Fin 2) ℂ) 0 0 * a + (M : Matrix (Fin 2) (Fin 2) ℂ) 0 1 * b) /
          ((M : Matrix (Fin 2) (Fin 2) ℂ) 1 0 * a + (M : Matrix (Fin 2) (Fin 2) ℂ) 1 1 * b) : ℂ)
          : OnePoint ℂ) :=
  sl2c_weylRatio M a b hb hden

/-! ## §E — assembled -/

/-- **[The Madelung wave function, geometrically resolved].** For the electron spinor `χ`, a spacetime point
`x` (Hermitian), and a global phase `u` (`|u| = 1`):

* **amplitude** `R² = hopfIntensity χ = |χ₀|² + |χ₁|²` (Hopf/Born intensity);
* **phase** is the `S¹` Hopf fiber — it fixes the Bloch base `hopfBase (u·χ) = hopfBase χ`;
* the spinor + point `(i·x·χ, χ)` is a **null twistor**;
* the direction `weylRatio χ` is a `CP¹` point, phase-invariant.

The Madelung `ψ = R e^{iS}` is one spinor resolved through the Hopf fibration, the Wilson-loop phase, the
Penrose twistor, and the `SL(2,ℂ)` Möbius sphere. -/
theorem madelung_geometric_resolution (χ : Fin 2 → ℂ) (x : Matrix (Fin 2) (Fin 2) ℂ)
    (hx : ∀ i j, x i j = (starRingEnd ℂ) (x j i)) (u : ℂ) (hu₁ : star u * u = 1) (hu₀ : u ≠ 0) :
    hopfIntensity χ = ((Complex.normSq (χ 0) + Complex.normSq (χ 1) : ℝ) : ℂ)
      ∧ hopfBase (phaseRotate u χ) = hopfBase χ
      ∧ IsNullTwistor (Complex.I • (x *ᵥ χ), χ)
      ∧ twistorDirection (Complex.I • (x *ᵥ χ), χ) = weylRatio χ
      ∧ weylRatio (u • χ) = weylRatio χ :=
  ⟨madelung_amplitude_is_hopfIntensity χ, hopfBase_phase_invariant u χ hu₁,
    incident_isNull (Complex.I • (x *ᵥ χ), χ) x hx rfl, rfl, weylRatio_smul u hu₀ χ⟩

end Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronMadelungGeometricResolution

end

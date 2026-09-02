/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.HorizonNagaoContourBitEinstein
public import Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.FisherRaoGaussianLeviCivita

/-!
# Stachel's gravitational superpotential is the constant-curvature kernel, with `G` in bit form

Stachel (Gen. Relativ. Gravit. 8 (1977) 705) gives a generalised Palatini variational principle whose
independent fields are the metric `g_μν`, the affine connection `Γ^κ_μν`, a fully covariant Riemann
tensor `R_μνκλ`, and a rank-four tensor density — the **gravitational "superpotential"**
`S̃^{βκλα} = (−g)^{1/2}(g^{βα} g^{κλ} − g^{βλ} g^{κα})` (Eq. 2.3). Varying the Lagrangian recovers the
Levi-Civita connection (Eq. 2.4′), the Riemann tensor (Eq. 2.2), and the **Einstein field equations**
`G^{μν} = k T^{μν}` (Eq. 2.5′), with `k` the gravitational coupling constant.

The **kernel of the superpotential** — the antisymmetric metric bivector `g^{βα} g^{κλ} − g^{βλ}
g^{κα}` — is exactly the `(gg − gg)` structure of `constantCurvature`
(`Curvature.RiemannCurvatureTensor.constantCurvature K g = K(g_{ac} g_{bd} − g_{ad} g_{bc})`), the
Riemann tensor of a maximally symmetric space. So Stachel's superpotential is
`−constantCurvature 1 g`: **the object whose divergence gives the Komar conservation laws is (minus)
the constant-curvature Riemann kernel**, the very tensor used for the Fisher-Rao curvature
`FisherRaoGaussianLeviCivita.frRiemann σ = constantCurvature (−1/2)(frMetric σ)`. The superpotential of
conservation and the curvature of maximal symmetry are one algebraic object.

Stachel's coupling `k` is the Einstein coupling `κ = 8πG/c⁴`; from the holographic bit count
`N = holographicBits (sphereArea R) G ℏ c` it is the area-per-bit form
`κ = 8π(A/N)/(ℏc)` (`einsteinCoupling_bitForm`). So the variational Einstein equation and its `G` are
carried through to the bit form of this arc.

* **§A** the superpotential kernel and its identity `S̃ = −constantCurvature 1 g`; its Riemann
  symmetries (`IsRiemannCurvature`).
* **§B** `constantCurvature K g = −K · S̃`, and the Fisher-Rao curvature as a scaled superpotential.
* **§C** the variational Einstein equation `G_μν = κ T_μν` with `κ = 8πG/c⁴ = 8π(A/N)/(ℏc)`.
* **§D** the capstone: Stachel's variational output — a Riemann-symmetric superpotential, the Einstein
  equation, and the coupling in bit form — from one metric and one bit count.

## References

* J. Stachel, *A variational principle giving gravitational "superpotentials," the affine connection,
  Riemann tensor, and Einstein field equations*, Gen. Relativ. Gravit. 8 (1977) 705 — Eqs. 2.1–2.5.
* A. Komar, Phys. Rev. 113 (1959) 934; L. D. Landau, E. M. Lifshitz, *The Classical Theory of Fields*
  — the superpotential and its conservation law.
-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EinsteinFieldEquationsPhysLean
open Physlib.QuantumMechanics.ComplexAction.EntropicTime.FisherRaoGaussianLeviCivita
open Physlib.Thermodynamics
open Physlib.Thermodynamics.GravitationalCouplingSystem

namespace Physlib.QuantumMechanics.ComplexAction.EntropicTime.StachelSuperpotentialEinsteinBits

variable {ι : Type*}

@[expose] public section

/-! ## A. The superpotential kernel is the constant-curvature Riemann kernel -/

/-- **[Stachel's gravitational superpotential kernel, Eq. 2.3]** the antisymmetric metric bivector
`S̃^{βκλα} = g^{βα} g^{κλ} − g^{βλ} g^{κα}` (the tensor-density weight `(−g)^{1/2}` is a scalar factor,
omitted from the kernel). It has the index symmetries of a Riemann tensor. -/
def stachelSuperpotential (g : Matrix ι ι ℝ) : RiemannTensor ι :=
  fun a b c d => g a d * g b c - g a c * g b d

/-- **[The superpotential is minus the constant-curvature kernel]**
`S̃ = −constantCurvature 1 g`. Stachel's superpotential (from varying the Riemann tensor) is, up to a
sign, the `(gg − gg)` Riemann tensor of a maximally symmetric space. -/
theorem stachelSuperpotential_eq_neg_constantCurvature (g : Matrix ι ι ℝ) (a b c d : ι) :
    stachelSuperpotential g a b c d = -constantCurvature 1 g a b c d := by
  simp only [stachelSuperpotential, constantCurvature]; ring

/-- **[The superpotential has the Riemann index symmetries]** for a symmetric metric the superpotential
kernel is antisymmetric in each pair, symmetric under pair exchange, and satisfies the first Bianchi
identity — it is a bona fide Riemann-type tensor (`IsRiemannCurvature`), as required of the field
`R_μνκλ` it dualises. -/
theorem stachelSuperpotential_isRiemann (g : Matrix ι ι ℝ) (hsymm : ∀ i j, g i j = g j i) :
    IsRiemannCurvature (stachelSuperpotential g) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> intro a b c d <;> simp only [stachelSuperpotential]
  · ring
  · ring
  · rw [hsymm c b, hsymm d a, hsymm c a, hsymm d b]; ring
  · rw [hsymm c b, hsymm d b, hsymm d c]; ring

/-! ## B. Constant curvature and the Fisher-Rao curvature as scaled superpotentials -/

/-- **[Constant-curvature Riemann is minus `K` times the superpotential]**
`constantCurvature K g = −K · S̃`. A maximally symmetric curvature is a rescaled gravitational
superpotential. -/
theorem constantCurvature_eq_neg_smul_stachel (K : ℝ) (g : Matrix ι ι ℝ) (a b c d : ι) :
    constantCurvature K g a b c d = -K * stachelSuperpotential g a b c d := by
  simp only [constantCurvature, stachelSuperpotential]; ring

/-- **[The Fisher-Rao curvature is half the superpotential of its metric]**
`frRiemann σ = ½ · S̃(frMetric σ)`. The maximally symmetric Fisher-Rao Riemann tensor
(`constantCurvature (−1/2)(frMetric σ)`) is the Stachel superpotential of the Fisher-Rao metric scaled
by `1/2`: the information-geometry curvature and the gravitational superpotential are the same
bivector. -/
theorem frRiemann_eq_half_stachel (σ : ℝ) (a b c d : Fin 2) :
    frRiemann σ a b c d = (1 / 2) * stachelSuperpotential (frMetric σ) a b c d := by
  simp only [frRiemann, constantCurvature, stachelSuperpotential]; ring

/-! ## C. The variational Einstein equation with `G` in area-per-bit form -/

/-- **[Stachel's variational Einstein equation in bit form, Eq. 2.5′]** varying the metric produces
`G_μν = k T_μν` (`einsteinFieldEquation`) with `k` the gravitational coupling; at `k = 8πG/c⁴` and the
holographic bit count `N = holographicBits (sphereArea R) G ℏ c` the coupling is the area-per-bit form
`8π(A/N)/(ℏc)` (`einsteinCoupling_bitForm`). Stachel's variational `k` is the entropic screen's coupling. -/
theorem stachel_variational_efe_bitForm (Ric : Matrix ι ι ℝ) (scalarR : ℝ)
    (g T : Matrix ι ι ℝ) (G ℏ c N R : ℝ)
    (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0) (hR : R ≠ 0)
    (hbits : N = holographicBits (sphereArea R) G ℏ c)
    (hEFE : einsteinFieldEquation Ric scalarR g T (8 * Real.pi * G / c ^ 4)) :
    einsteinFieldEquation Ric scalarR g T (8 * Real.pi * G / c ^ 4)
    ∧ 8 * Real.pi * G / c ^ 4 = 8 * Real.pi * (sphereArea R / N) / (ℏ * c) :=
  ⟨hEFE, einsteinCoupling_bitForm G ℏ c N R hℏ hc hG hR hbits⟩

/-! ## D. The variational output in bit form -/

/-- **[Stachel's variational principle in bit form]** from one symmetric metric `g` and the single
identification `N = holographicBits (sphereArea R) G ℏ c`, the variational principle delivers together:
the gravitational **superpotential** as a Riemann-symmetric bivector (`IsRiemannCurvature`); the
**Einstein field equation** `G_μν = κ T_μν`; and the coupling `κ = 8πG/c⁴ = 8π(A/N)/(ℏc)` in the
area-per-bit form of this arc. Connection, curvature, superpotential, field equation and the
information-theoretic `G`, one variational statement. -/
theorem stachel_variational_gravity_bitForm (g : Matrix ι ι ℝ)
    (Ric : Matrix ι ι ℝ) (scalarR : ℝ) (T : Matrix ι ι ℝ) (G ℏ c N R : ℝ)
    (hsymm : ∀ i j, g i j = g j i)
    (hℏ : ℏ ≠ 0) (hc : c ≠ 0) (hG : G ≠ 0) (hR : R ≠ 0)
    (hbits : N = holographicBits (sphereArea R) G ℏ c)
    (hEFE : einsteinFieldEquation Ric scalarR g T (8 * Real.pi * G / c ^ 4)) :
    IsRiemannCurvature (stachelSuperpotential g)
    ∧ einsteinFieldEquation Ric scalarR g T (8 * Real.pi * G / c ^ 4)
    ∧ 8 * Real.pi * G / c ^ 4 = 8 * Real.pi * (sphereArea R / N) / (ℏ * c) :=
  ⟨stachelSuperpotential_isRiemann g hsymm, hEFE,
    einsteinCoupling_bitForm G ℏ c N R hℏ hc hG hR hbits⟩

end

end Physlib.QuantumMechanics.ComplexAction.EntropicTime.StachelSuperpotentialEinsteinBits

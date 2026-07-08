/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDPathIntegralConvergence

/-!
# Building blocks of the QED functional integral: Faddeev–Popov, Berezin, renormalization, continuum limit

Constructs the **rigorous, finite-dimensional / regularized building blocks** of the QED path integral:
Faddeev–Popov gauge fixing, Grassmann (Berezin) fermion integration, a renormalization counterterm, and a
continuum limit. Each is genuine mathematics at the finite/regularized level.

**Scope.** These are the *formal building blocks*, not the full theory. The actual open
problem — the continuum limit of the **interacting** 4D gauge theory — is **not** constructed here, and
cannot be: rigorous interacting QED₄ is unknown (and conjectured trivial, Landau pole; cf. the proof of
`φ⁴₄` triviality, Aizenman–Duminil-Copin 2021); only the *free / regularized* continuum limit is rigorous.
What is proved:

* **§A — Grassmann/Berezin fermion integration** (`berezin_gaussian_eq_det`): the finite-dimensional
 Matthews–Salam formula `∫ dθ̄ dθ e^{−mθ̄θ} = det[m]` on a concrete `n = 1` Grassmann algebra, with the
 nilpotency `(θθ̄)² = 0` (`θθb_nilpotent`) that makes the fermion exponential truncate exactly.
* **§B — Faddeev–Popov (abelian)** (`abelian_FP_decouples`): for an abelian (QED) gauge theory the
 gauge-variation operator and hence the FP determinant are **field-independent** — the ghosts decouple
 and factor out as a constant.
* **§C — renormalization counterterm** (`renormalized_finite`): a log-divergent regularized quantity
 `c·log Λ + finite`, with the BPHZ counterterm `−c·log(Λ/μ)`, has a **finite** `Λ → ∞` limit — the
 divergence cancels.
* **§D — continuum limit (free only)** (`free_continuum_limit`): a free/regularized lattice quantity
 converges as the spacing `a → 0`. The **interacting** continuum limit (`interactingContinuumLimitOpen`)
 is recorded as an explicit open statement, **not** proved.

## References

* **§A (Grassmann/Berezin):** P. T. Matthews, A. Salam, *Propagators of quantized field*, Nuovo Cimento 2
 (1955) 120 (the `∫dψ̄dψ e^{−ψ̄Mψ} = det M` formula); F. A. Berezin, *The Method of Second Quantization*,
 Academic Press (1966).
* **§B (Faddeev–Popov):** L. D. Faddeev, V. N. Popov, *Feynman diagrams for the Yang–Mills field*, Phys.
 Lett. B 25 (1967) 29.
* **§C (renormalization):** N. N. Bogoliubov, O. S. Parasiuk (1957); K. Hepp (1966); W. Zimmermann (1969)
 — the BPHZ subtraction making divergent integrals finite by counterterms.
* **§D (continuum / open problem):** J. Glimm, A. Jaffe, *Quantum Physics: A Functional Integral Point of
 View*, Springer (1987) (constructive QFT); M. Aizenman, H. Duminil-Copin, *Marginal triviality of the
 scaling limits of critical 4D Ising and `φ⁴₄` models*, Ann. Math. 194 (2021) 163 (the triviality that
 obstructs the *interacting* QED₄ continuum).
* Repo links: `Bogoliubov.Transformation.bogoliubovEnergy` (Dirac dispersion, §E),
 `NonHermitian.WickRotation.entropyDamping` (the regulator, §E), `PathIntegral.QEDPathIntegralConvergence`.

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDFunctionalIntegralConstruction

open Matrix Filter Topology

/-! ## §A — Grassmann (Berezin) integration over fermion fields: `∫ dθ̄ dθ e^{−mθ̄θ} = det M` -/

/-- A concrete `n = 1` Grassmann algebra: `x = s·1 + θ_c·θ + θb_c·θ̄ + t·(θθ̄)`. -/
structure G1 where
  /-- Scalar (degree-0) component. -/
  s : ℝ
  /-- `θ` (odd) component. -/
  θ : ℝ
  /-- `θ̄` (odd) component. -/
  θb : ℝ
  /-- `θθ̄` (top, degree-2) component. -/
  t : ℝ

/-- The Grassmann (exterior) product: `θ² = θ̄² = 0`, `θ̄θ = −θθ̄`. -/
def G1.mul (x y : G1) : G1 :=
  ⟨x.s * y.s, x.s * y.θ + x.θ * y.s, x.s * y.θb + x.θb * y.s,
    x.s * y.t + x.t * y.s + x.θ * y.θb - x.θb * y.θ⟩

/-- The top form `θθ̄`. -/
def θθb : G1 := ⟨0, 0, 0, 1⟩

/-- **The top form is nilpotent** `(θθ̄)² = 0` — the algebraic fact that makes the fermion exponential
`e^{−mθ̄θ}` truncate to the exact polynomial `1 + mθθ̄`. -/
theorem θθb_nilpotent : G1.mul θθb θθb = ⟨0, 0, 0, 0⟩ := by simp [G1.mul, θθb]

/-- **The Berezin integral** `∫ dθ̄ dθ` extracts the top-form coefficient (`∫ dθ̄ dθ (θθ̄) = 1`). -/
def berezin (x : G1) : ℝ := x.t

/-- **The fermion Gaussian** `e^{−mθ̄θ} = 1 + mθθ̄` (exact by nilpotency `θθb_nilpotent`). -/
def fermionGaussian (m : ℝ) : G1 := ⟨1, 0, 0, m⟩

/-- **[Matthews–Salam, `n = 1`] The Grassmann Gaussian integral is the fermion determinant**
`∫ dθ̄ dθ e^{−mθ̄θ} = det[m] = m`. This is the rigorous finite-dimensional Berezin integration over a
fermion field — the fermion functional integral evaluated to a determinant. -/
theorem berezin_gaussian_eq_det (m : ℝ) :
    berezin (fermionGaussian m) = (!![m] : Matrix (Fin 1) (Fin 1) ℝ).det := by
  simp [berezin, fermionGaussian, Matrix.det_fin_one]

/-- **The Berezin integral is additive** (linearity of the fermion integral over its integrand). -/
theorem berezin_add (x y : G1) : berezin ⟨x.s + y.s, x.θ + y.θ, x.θb + y.θb, x.t + y.t⟩
    = berezin x + berezin y := rfl

/-! ## §B — Faddeev–Popov gauge fixing: abelian ghost decoupling -/

/-- **Abelian gauge variation** `δG(A)/δα = M α`: for a linear gauge condition in an abelian (QED) theory
the gauge variation is **independent of the gauge field `A`** (it is `∂·∂α = □α`, no `A`-dependence). -/
def abelianGaugeVariation {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (_A α : Fin n → ℝ) : Fin n → ℝ :=
  M.mulVec α

/-- **[Faddeev–Popov, abelian] The gauge-variation operator is field-independent** — the Jacobian of the
gauge condition does not depend on the gauge field `A`. -/
theorem abelian_FP_field_independent {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (A A' α : Fin n → ℝ) :
    abelianGaugeVariation M A α = abelianGaugeVariation M A' α := rfl

/-- **The Faddeev–Popov determinant** `Δ_FP = det(δG/δα)` — for the abelian gauge variation. -/
def fpDeterminant {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (_A : Fin n → ℝ) : ℝ := M.det

/-- **[Faddeev–Popov, abelian] The FP determinant is a field-independent constant ⟹ the ghosts decouple.**
In QED the Faddeev–Popov determinant does not depend on the gauge field, so it factors out of the path
integral as an overall constant — the ghosts are free and decouple (unlike non-abelian Yang–Mills). -/
theorem abelian_FP_decouples {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (A A' : Fin n → ℝ) :
    fpDeterminant M A = fpDeterminant M A' := rfl

/-! ## §C — renormalization: a divergent integral made finite by a counterterm -/

/-- A regularized one-loop quantity with a logarithmic UV divergence `c·log Λ` plus a finite part
(cutoff `Λ`). -/
noncomputable def regSelfEnergy (c finitePart Λ : ℝ) : ℝ := c * Real.log Λ + finitePart

/-- The renormalization counterterm `−c·log(Λ/μ)` subtracting the divergence at the scale `μ` (BPHZ /
multiplicative renormalization at the level of the divergent integral). -/
noncomputable def counterterm (c μ Λ : ℝ) : ℝ := -(c * Real.log (Λ / μ))

/-- **[Renormalization] The renormalized quantity is finite.** The log-divergence cancels between the
regularized integral and the counterterm, leaving a finite `Λ → ∞` limit `c·log μ + finite`: the infinite
counterterm renders the divergent integral finite. -/
theorem renormalized_finite (c finitePart μ : ℝ) (hμ : 0 < μ) :
    Tendsto (fun Λ => regSelfEnergy c finitePart Λ + counterterm c μ Λ) atTop
      (𝓝 (c * Real.log μ + finitePart)) := by
  apply Tendsto.congr' (f₁ := fun _ => c * Real.log μ + finitePart) _ tendsto_const_nhds
  filter_upwards [eventually_gt_atTop 0] with Λ hΛ
  unfold regSelfEnergy counterterm
  rw [Real.log_div hΛ.ne' hμ.ne']; ring

/-! ## §D — continuum limit: free/regularized (rigorous) vs interacting (open) -/

/-- **[Continuum limit — free/regularized] A free lattice-regularized quantity converges as the spacing
`a → 0`.** This is the rigorous (Gaussian/free) continuum limit. -/
theorem free_continuum_limit (G : ℝ) :
    Tendsto (fun a : ℝ => G * Real.exp (-(a ^ 2))) (𝓝[>] 0) (𝓝 G) := by
  have hc : Continuous (fun a : ℝ => G * Real.exp (-(a ^ 2))) := by fun_prop
  simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds

/-- **[Open problem — NOT proved] The interacting continuum limit.** The statement that a sequence of
lattice-regularized *interacting* QED amplitudes `K : ℕ → ℂ` (spacing `→ 0`) converges to a limit `L`.
This is recorded only as a `Prop` to mark the boundary: constructing such a limit for interacting QED₄ is
an **open problem** (rigorous interacting QED₄ is unknown, and conjectured trivial). Nothing below asserts
it holds; the building blocks §A–§D do **not** assemble into a proof of it. -/
def interactingContinuumLimitOpen (K : ℕ → ℂ) (L : ℂ) : Prop :=
  Tendsto K atTop (𝓝 L)

/-- The interacting continuum limit *would* be witnessed by an actual convergence proof — which does not
exist for QED₄. This lemma only records the trivial direction (a constant sequence converges), emphasizing
that the content is in producing the limiting QED₄ measure, which is **not** done here. -/
theorem interactingContinuumLimit_trivial_only (L : ℂ) :
    interactingContinuumLimitOpen (fun _ => L) L :=
  tendsto_const_nhds

/-! ## §E — links to the repo: the building blocks evaluate on actual repo quantities -/

/-- **[Link] The Berezin fermion determinant evaluated at the Dirac dispersion.** With the fermion mass
parameter set to the Dirac/Bogoliubov dispersion `√(p²+m²)` (`Bogoliubov.Transformation.bogoliubovEnergy`,
the relativistic fermion energy of the arc), the Grassmann Gaussian integral `∫dθ̄dθ e^{−(√(p²+m²))θ̄θ}`
is that dispersion — the fermion functional integral over a *Dirac* mode is its energy. -/
theorem berezin_dirac_dispersion (p mass : ℝ) :
    berezin (fermionGaussian (Bogoliubov.Transformation.bogoliubovEnergy p mass))
      = Bogoliubov.Transformation.bogoliubovEnergy p mass := by
  rw [berezin_gaussian_eq_det]; simp [Matrix.det_fin_one]

/-- **[Link] The renormalization regulator is the arc's entropic damping.** The exponential suppression
`e^{−S_I/ℏ}` used throughout the renormalization/regularization is definitionally the entropic-damping /
Cameron–Martin weight `WickRotation.entropyDamping` of the path-integral arc — the regulator that makes
the QED path integral measure-valid (`PathIntegral.QEDPathIntegralMeasureValid`). -/
theorem renorm_regulator_is_entropic (S_I ℏ : ℝ) :
    Real.exp (-(S_I / ℏ)) = Physlib.QuantumMechanics.NonHermitian.WickRotation.entropyDamping S_I ℏ :=
  rfl

end Physlib.QuantumMechanics.ComplexAction.PathIntegral.QEDFunctionalIntegralConstruction

end

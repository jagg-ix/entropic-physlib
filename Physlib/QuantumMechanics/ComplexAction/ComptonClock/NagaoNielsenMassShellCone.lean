/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.EquivalencePrincipleMassShell
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations

/-!
# The Nagao–Nielsen convergence cone is the mass-shell Minkowski form

In the Nagao–Nielsen complex-coordinate formalism (K. Nagao, H. B. Nielsen, arXiv:1304.4017, §2), the
coordinate `q` and momentum `p` are **complex** (`q̂†_new|q⟩_new = q|q⟩_new` for complex `q`, Eq. 2.1–2.7).
The smeared complex delta function `δ_c^ε(q)` converges only for `q` in the region (Eq. 2.10)
  `L(q) ≡ (Re q)² − (Im q)² > 0`,
a **Minkowski `(1,1)` quadratic form** on the complex plane — the steepest-descent contours are the
"timelike" curves with tangent angle `|θ| < π/4` (Figs. 1–2).

This is the *same* Lorentzian quadratic form as the real mass-shell of
`ComptonClock.EquivalencePrincipleMassShell`, `(E/c)² − p² = (mc)²`, and of the tetrad
`minkowskiMatrix`. So the Nagao–Nielsen convergence cone (on the complexified coordinate) and the
tetrad mass-shell (on real spacetime) are one and the same `(1,n)` Minkowski structure — the complex route
uses its Lorentzian geometry as an analyticity/contour cone, the real route as a spacetime tetrad.

* **§A — the convergence cone (Eq. 2.10).** `nnLorentzForm` (`(Re q)²−(Im q)²`), `nnLorentzForm_eq_re_sq`
  (`= Re(q²)`), `nnConverges` (`> 0`, timelike).
* **§B — the cone is the mass-shell.** identifying `q = E/c + i·p`, `nnLorentzForm_energyMomentum`
  (`L(q) = (mc)²`) and `nnConverges_energyMomentum_iff` (the contour converges iff the particle is massive,
  `mc ≠ 0`) — the steepest-descent cone is the forward mass-shell.
* **§C — the complex-Einstein real/imaginary split.** `tetradInvariant_real_rest_energy`
  (`Re(complexEinsteinEnergy) = m_R c²`, the tetrad-gauge-invariant rest energy) and
  `entropicDamping_imaginary_rest_energy` (`Im = m_I c²`, the non-geometric damping);
  `tetrad_massShell_uses_real_mass` shows the mass-shell depends only on `m_R`.
-/

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone

open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EntanglementReparametrization
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.EquivalencePrincipleMassShell
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations

/-! ## §A — the Nagao–Nielsen convergence cone (Eq. 2.10) -/

/-- **The Nagao–Nielsen convergence quadratic form** `L(q) = (Re q)² − (Im q)²` (Eq. 2.10): a Minkowski
`(1,1)` form on the complexified coordinate, whose positivity is the condition for the smeared complex
delta `δ_c^ε(q)` to converge. -/
def nnLorentzForm (q : ℂ) : ℝ := q.re ^ 2 - q.im ^ 2

/-- **The convergence form is the real part of the square** `L(q) = Re(q²)`: the Minkowski `(1,1)` form is
`Re(q²) = (Re q)² − (Im q)²`. -/
theorem nnLorentzForm_eq_re_sq (q : ℂ) : nnLorentzForm q = (q ^ 2).re := by
  unfold nnLorentzForm
  rw [pow_two q, Complex.mul_re]; ring

/-- **The Nagao–Nielsen convergence condition** `L(q) > 0` (Eq. 2.10): the "timelike" region of the
`(1,1)` cone, in which the steepest-descent contour of the complex delta function may be laid. -/
def nnConverges (q : ℂ) : Prop := 0 < nnLorentzForm q

/-! ## §B — the convergence cone is the real mass-shell -/

/-- **The energy–momentum as a complex coordinate** `q = E/c + i·p`, with `E = √((mc²)²+(pc)²)` the full
Einstein energy: real part energy, imaginary part momentum. -/
noncomputable def energyMomentumComplex (m c p : ℝ) : ℂ :=
  ⟨einsteinEnergy m c p / c, p⟩

/-- **The Nagao–Nielsen convergence form of the energy–momentum coordinate is the mass-shell**
`L(E/c + i·p) = (mc)²`: the complex-coordinate cone `(Re q)² − (Im q)²` evaluated on `q = E/c + i·p` is
exactly the real Lorentz invariant `(E/c)² − p² = (mc)²` of
`EquivalencePrincipleMassShell.einstein_massShell`. -/
theorem nnLorentzForm_energyMomentum (m c p : ℝ) (hc : c ≠ 0) :
    nnLorentzForm (energyMomentumComplex m c p) = (m * c) ^ 2 := by
  unfold nnLorentzForm energyMomentumComplex
  exact einstein_massShell m c p hc

/-- **The steepest-descent contour converges iff the particle is massive** `nnConverges ↔ mc ≠ 0`: the
Nagao–Nielsen `(1,1)` convergence cone is precisely the forward mass-shell — a real, massive particle
`(mc)² > 0` is a "timelike" point of the complex-coordinate cone. -/
theorem nnConverges_energyMomentum_iff (m c p : ℝ) (hc : c ≠ 0) :
    nnConverges (energyMomentumComplex m c p) ↔ m * c ≠ 0 := by
  unfold nnConverges
  rw [nnLorentzForm_energyMomentum m c p hc]
  constructor
  · intro h heq; rw [heq] at h; norm_num at h
  · intro h; positivity

/-! ## §C — the complex-Einstein real/imaginary split (tetrad gauges only the real mass) -/

/-- **The tetrad-gauge-invariant rest energy is the real part** `Re(complexEinsteinEnergy) = m_R c²`: of
the complex mass `m = m_R + i m_I`, only the real part `m_R` gives the ordinary rest energy that the real
tetrad / real Lorentz group protects (`fourMomentum_norm_tetrad_gauge_invariant`). -/
theorem tetradInvariant_real_rest_energy (m_R m_I c : ℝ) :
    (complexEinsteinEnergy m_R m_I c).re = m_R * c ^ 2 :=
  complexEinsteinEnergy_re m_R m_I c

/-- **The imaginary part is the non-geometric entropic damping** `Im(complexEinsteinEnergy) = m_I c²`:
the imaginary mass `m_I` is the dissipative energy that drives `exp(−m_I c² σ/ℏ)`, encoded in the complex
action rather than the tetrad geometry. -/
theorem entropicDamping_imaginary_rest_energy (m_R m_I c : ℝ) :
    (complexEinsteinEnergy m_R m_I c).im = m_I * c ^ 2 :=
  complexEinsteinEnergy_im m_R m_I c

/-- **The mass-shell depends only on the real mass** `L(E/c + i·p) = (m_R c)²`: the tetrad-gauge-invariant
mass-shell is built from `m_R = Re(m)` alone; the imaginary mass `m_I` (entropic damping) never enters the
Minkowski invariant, so the tetrad gauges only the real mass. -/
theorem tetrad_massShell_uses_real_mass (m_R c p : ℝ) (hc : c ≠ 0) :
    nnLorentzForm (energyMomentumComplex m_R c p) = (m_R * c) ^ 2 :=
  nnLorentzForm_energyMomentum m_R c p hc

end Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone

end

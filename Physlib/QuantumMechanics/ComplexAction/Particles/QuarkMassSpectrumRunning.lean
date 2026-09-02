/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel

/-!
# Quark mass spectrum and the running of the strong coupling

The six quark masses (PDG), attached to the existing `HadronFlavorModel.QuarkFlavor`, and the one-loop
running of `α_s` — filling the "individual quark masses / α_s running" gap. The masses are **data**; the
running is a genuine **theorem** (asymptotic freedom).

* **§A — the quark mass spectrum.** `quarkMass : QuarkFlavor → ℝ` (MeV) with the mass hierarchy
  `m_u < m_d < m_s < m_c < m_b < m_t` (`quark_mass_hierarchy`) and the isospin splitting `m_u < m_d`
  (`up_lighter_than_down`).
* **§B — the one-loop β-function.** The QCD coefficient `b₀ = 11 − 2n_f/3` is **positive** for
  `n_f ≤ 16` (`asymptotic_freedom_coefficient`); the β-function `β = −b₀ α_s²/(2π)` is **negative**
  (`betaFunction_neg`) — the coupling decreases with energy.
* **§C — the running coupling.** `α_s(t) = α_s(0)/(1 + b₀ α_s(0) t/(2π))` (`t = ln(μ/μ₀)`) **decreases**
  as the scale rises (`alphaS_decreases`) — asymptotic freedom; and it satisfies the multiplicative
  group law only through this pole structure.

**Honest layering.** Proven: the mass hierarchy, the positivity of `b₀`, and the monotone decrease of the
one-loop running coupling (asymptotic freedom). Interpretive: the quark masses are scheme-dependent
empirical inputs (PDG `MS̄`/pole values); the one-loop `β`-function is the leading QCD result taken as
the model.

## References

* Particle Data Group, PTEP 2022, 083C01 (quark masses); D. Gross, F. Wilczek; H. D. Politzer
  (asymptotic freedom, `b₀ = 11 − 2n_f/3`). Reuses `HadronFlavorModel.QuarkFlavor`.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.QuarkMassSpectrumRunning

open Physlib.QuantumMechanics.ComplexAction.Particles.HadronFlavorModel


/-- **The quark masses** (PDG, MeV): `m_u ≈ 2.16`, `m_d ≈ 4.67`, `m_s ≈ 93.4` (`MS̄` at 2 GeV);
`m_c ≈ 1270`, `m_b ≈ 4180` (`MS̄`), `m_t ≈ 172690` (pole). -/
def quarkMass : QuarkFlavor → ℝ
  | .up => 2.16
  | .down => 4.67
  | .strange => 93.4
  | .charm => 1270
  | .bottom => 4180
  | .top => 172690

/-- **The quark mass hierarchy** `m_u < m_d < m_s < m_c < m_b < m_t` — six flavors of strictly
increasing mass. -/
lemma quark_mass_hierarchy :
    quarkMass .up < quarkMass .down ∧ quarkMass .down < quarkMass .strange ∧
      quarkMass .strange < quarkMass .charm ∧ quarkMass .charm < quarkMass .bottom ∧
        quarkMass .bottom < quarkMass .top := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [quarkMass]

/-- **The up quark is lighter than the down quark** `m_u < m_d`: the isospin mass splitting responsible
(with electromagnetism) for the proton being lighter than the neutron. -/
lemma up_lighter_than_down : quarkMass .up < quarkMass .down := by
  norm_num [quarkMass]


/-- **The one-loop β-function coefficient** `b₀ = 11 − 2n_f/3` (Gross–Wilczek–Politzer), for `n_f`
active quark flavors. -/
noncomputable def betaZero (nf : ℕ) : ℝ := 11 - 2 * (nf : ℝ) / 3

/-- **Asymptotic freedom holds for `n_f ≤ 16`** `b₀ > 0`: for up to sixteen flavors (in particular the
six of the Standard Model) the one-loop coefficient is positive, so QCD is asymptotically free. -/
lemma asymptotic_freedom_coefficient (nf : ℕ) (h : nf ≤ 16) : 0 < betaZero nf := by
  have : (nf : ℝ) ≤ 16 := by exact_mod_cast h
  unfold betaZero; linarith

/-- **The β-function is negative** `β = −b₀ α_s²/(2π) < 0` for `b₀ > 0` and `α_s ≠ 0`: the strong
coupling decreases as the renormalization scale increases. -/
noncomputable def betaFunction (b0 αs : ℝ) : ℝ := -b0 * αs ^ 2 / (2 * Real.pi)

lemma betaFunction_neg (b0 αs : ℝ) (hb : 0 < b0) (hαs : αs ≠ 0) :
    betaFunction b0 αs < 0 := by
  have hsq : 0 < αs ^ 2 := by positivity
  have hden : 0 < 2 * Real.pi := by positivity
  unfold betaFunction
  apply div_neg_of_neg_of_pos _ hden
  nlinarith [mul_pos hb hsq]


/-- **The one-loop running coupling** `α_s(t) = α_s(0)/(1 + b₀ α_s(0) t/(2π))`, with `t = ln(μ/μ₀)` the
logarithmic scale. -/
noncomputable def alphaSRun (α0 b0 t : ℝ) : ℝ := α0 / (1 + b0 * α0 * t / (2 * Real.pi))

/-- **Asymptotic freedom: the running coupling decreases with scale** `α_s(t) < α_s(0)` for `t > 0`
(higher energy), positive coupling and positive `b₀`: the denominator exceeds one, so `α_s` shrinks
toward zero at large momenta. -/
lemma alphaS_decreases (α0 b0 t : ℝ) (hα : 0 < α0) (hb : 0 < b0) (ht : 0 < t) :
    alphaSRun α0 b0 t < α0 := by
  have hnum : 0 < b0 * α0 * t := mul_pos (mul_pos hb hα) ht
  have hden : 0 < 2 * Real.pi := by positivity
  have hpos : 0 < b0 * α0 * t / (2 * Real.pi) := div_pos hnum hden
  unfold alphaSRun
  exact div_lt_self hα (by linarith)

end Physlib.QuantumMechanics.ComplexAction.Particles.QuarkMassSpectrumRunning

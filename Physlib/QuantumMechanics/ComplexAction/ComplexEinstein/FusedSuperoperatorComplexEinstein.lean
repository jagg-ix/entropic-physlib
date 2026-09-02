/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMLorentzCombinedSuperoperator
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations

/-!
# The fused Lorentz–EM superoperator `𝒢_{J,F} = ad_{J+F}` and the complex Einstein equations

Links the fused Lorentz–EM superoperator `𝒢_{J,F} = ad_{J+F}` — the repo's canonical
`Electromagnetic.EMLorentzCombinedSuperoperator.emLorentzGenerator` (whose `𝔰𝔬(1,3)` Lie-algebra layer is
`AlgebraicQFTQuasifree.KleinGordonProgram` §F) — to the **complex (complex-action/entropic-time) Einstein field equations**
(`ComplexEinstein.ComplexMassEinsteinEquations`, `Electromagnetic.EMLorentzCombinedSuperoperator`).

The combined superoperator `emLorentzGenerator J F = emFieldAdjoint (J + F)` has, as its complex,
time-evolution form, the **covariant Liouvillian** `𝓛_{H+F} = −i[H+F,·]`. That combined Liouvillian carries
the complex Einstein structure: with a complex mass `m = m_R + i·m_I` (complex Hamiltonian `H = H_R − i·H_I`)
the generator splits

  `𝓛_{(H_R−iH_I)+F}(Y) = −i[H_R+F, Y]  −  [H_I, Y]`

into a **reversible** part (`−i[H_R+F,·]`, the real Einstein evolution) and an **entropic** part
(`−[H_I,·]`), and the entropic source is exactly the **imaginary Einstein energy**
`Im(E) = Im((m_R+i m_I)c²) = m_I c²` — the `Λ`/`T_I` term of the complex Einstein equation.

So the fused Lorentz–EM superoperator, complexified, *is* the complex-Einstein Liouvillian: gravity/Lorentz
(`J`/`H_R`) and electromagnetism (`F`) fuse into `ad_{J+F}`, and the imaginary part of the complex-action/entropic-time complex
Einstein mass is precisely its dissipative (entropy-producing) part.

* `fused_entropic_eq_imaginary_einstein` — the entropic gap `m_I c²` equals `Im(complexEinsteinEnergy)`.
* `fusedSuperoperator_complex_einstein` — the main result: the complexified combined Liouvillian splits into
  reversible (real Einstein) + entropic (imaginary Einstein), the entropic source being `Im(E)`.

## References

* complex-action/entropic-time complex Einstein equations — `ComplexEinstein.ComplexMassEinsteinEquations` (`complexMass`, `complexEinsteinEnergy`,
  `complexMass_einstein_equations`, `dirac_entropic_gap_eq_imaginary_einstein`);
  `Electromagnetic.EMLorentzCombinedSuperoperator` (`covariantLiouvillian_complex_decompose`).
* Repo carriers: `AlgebraicQFTQuasifree.KleinGordonProgram` (`fusedSuperop`, §F), `Electromagnetic.EMLorentzCombinedSuperoperator`
  (`emLorentzGenerator`, `covariantLiouvillian`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FusedSuperoperatorComplexEinstein

open Physlib.QuantumMechanics.ComplexAction.Electromagnetic.EMLorentzCombinedSuperoperator
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations

/-- **[Entropic gap = imaginary Einstein] `m_I c² = Im(E)`.** The entropic (dissipative) source of the
combined Lorentz–EM superoperator is the imaginary part of the complex Einstein energy
`E = (m_R + i·m_I)c²` (`dirac_entropic_gap_eq_imaginary_einstein`) — the `Λ`/`T_I` term of the complex-action/entropic-time
complex Einstein equation. -/
lemma fused_entropic_eq_imaginary_einstein (m_R m_I c : ℝ) :
    (m_I * c ^ 2 : ℝ) = (complexEinsteinEnergy m_R m_I c).im :=
  dirac_entropic_gap_eq_imaginary_einstein m_R m_I c

/-- **[Main result] the complexified fused superoperator is the complex-Einstein Liouvillian.** The combined
Lorentz–EM Liouvillian `𝓛_{(H_R−iH_I)+F}` (the complex, time-evolution form of `𝒢_{J,F}`) splits into a
**reversible** part `−i[H_R+F,·]` (real Einstein) and an **entropic** part `−[H_I,·]`, whose source is the
**imaginary Einstein energy** `m_I c² = Im(E)`. Gravity/Lorentz and electromagnetism fuse into `ad_{J+F}`, and
the imaginary part of the complex-action/entropic-time complex Einstein mass is its entropy-producing part. -/
lemma fusedSuperoperator_complex_einstein
    (H_R H_I F Y : Matrix (Fin 4) (Fin 4) ℂ) (m_R m_I c : ℝ) :
    covariantLiouvillian (H_R - Complex.I • H_I) F Y
        = -Complex.I • ((H_R + F) * Y - Y * (H_R + F)) - (H_I * Y - Y * H_I)
      ∧ (m_I * c ^ 2 : ℝ) = (complexEinsteinEnergy m_R m_I c).im :=
  ⟨covariantLiouvillian_complex_decompose H_R H_I F Y,
    dirac_entropic_gap_eq_imaginary_einstein m_R m_I c⟩

end Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.FusedSuperoperatorComplexEinstein

end

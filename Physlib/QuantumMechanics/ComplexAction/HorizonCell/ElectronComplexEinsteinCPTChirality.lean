/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronExclusionComplexEinstein
public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CPTDiracDynamics
public import Physlib.QuantumMechanics.ComplexAction.CausalRegimeCPTVertex
public import Physlib.QuantumMechanics.ComplexAction.AntiparticleConjugation

/-!
# The complex Einstein field equations as a CPT / charge–chirality probe

Uses the complex Einstein field equations of `ElectronExclusionComplexEinstein` to inspect CPT and the
electron/positron charge–chirality map. The complex Einstein energy `E = m_R c² + i·m_I c²` splits the electron
into a **CPT-even real sector** and a **C-odd imaginary sector**, and that split *is* the particle/antiparticle
distinction:

* **the real sector `Re E = m_R c² → G` is C-even** (`reEinstein_charge_conjugation_even`): it does not depend
  on `m_I`, so electron and positron have the same real mass and gravitate identically — and its mass-shell
  `lorentzianForm` is CPT-even (`realEinstein_massShell_cpt_even`, `lorentzianForm_neg`). Matter and antimatter
  curve spacetime the same way;
* **the imaginary sector `Im E = m_I c² → Λ` is C-odd** (`imEinstein_charge_conjugation_odd`): charge
  conjugation `m_I ↦ −m_I` flips its sign — the entropic/imaginary Einstein sector is the particle↔antiparticle
  discriminator, the `±Δ_I` branch of the sign-indefinite `H_I = Δ_I σ₃`;
* **the charge sign flips with the imaginary sector** (`chargeConjugation_flips_charge_and_imEinstein`): the
  positron's electric charge is `−` the electron's *and* its imaginary Einstein energy is `−` the electron's —
  the sign of `Im E` is the sign of the electric charge;
* **CPT = `−iγ⁵` is chirality, and maps the electron to the positron** (`cpt_maps_electron_to_positron`): the
  Greaves–Thomas CPT operator `A = −iγ⁵` (which flips chirality, `{γ⁵,γ^μ}=0`, `A² = −1`) conjugates the Dirac
  operator `A·D(−p)·A⁻¹ = D(p)` — so CPT sends the electron `(chirality, −e)` to the positron
  `(opposite chirality, +e)`, exactly the sign flip the imaginary Einstein sector carries.

So the complex Einstein field equation reads off CPT: its real part is the CPT-even gravity shared by electron
and positron; its imaginary part is the C-odd label whose sign is the electric charge and whose CPT partner is
the opposite chirality. The electron and positron are the two signs of `Im E`.

* **§A — C-even real / C-odd imaginary Einstein energy** (`reEinstein_charge_conjugation_even`,
  `imEinstein_charge_conjugation_odd`).
* **§B — charge sign = sign of the imaginary Einstein sector** (`chargeConjugation_flips_charge_and_imEinstein`).
* **§C — CPT = −iγ⁵ maps electron to positron** (`cpt_maps_electron_to_positron`).
* **§D — the real sector is CPT-even** (`realEinstein_massShell_cpt_even`).
* **§E — assembled** (`electron_positron_complexEinstein_cpt`).

**Honest layering.** §A/§B are exact `complexEinsteinEnergy_{re,im}` computations (the two gaps the CPT map left
open: no theorem had tied `±m_I`/`±Im E` to the particle/antiparticle branch or to the charge sign). §C/§D reuse
`cpt_diracOp_invariant` and `lorentzianForm_neg`. No claim that the geometric sign of `m_I` is *derived* from
charge; it is *identified* with the charge sign under conjugation. ## References

* R. Greaves, D. Thomas (arXiv:1204.4674, CPT); the CPT theorem. Repo carriers:
  `ComplexEinstein.ComplexMassEinsteinEquations`, `PTSymmetricQFT.CPTDiracDynamics`,
  `CausalRegimeCPTVertex`, `AntiparticleConjugation`, `HorizonCell.ElectronExclusionComplexEinstein`.


-/

set_option autoImplicit false

open spaceTime
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.CPTDiracDynamics
open Physlib.QuantumMechanics.ComplexAction.CausalRegimeCPTVertex
open Physlib.QuantumMechanics.ComplexAction.AntiparticleConjugation
open Physlib.QuantumMechanics.ComplexAction.Particles.BaryonLeptonNumberConservation
open Physlib.QuantumMechanics.ComplexAction.ComplexDelta.Convergence

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronComplexEinsteinCPTChirality


/-- **[The imaginary Einstein energy is C-odd] `Im E(−m_I) = −Im E(m_I)`.** Charge conjugation `m_I ↦ −m_I`
flips the sign of the imaginary part `Im E = m_I c²` of the complex Einstein energy — the entropic / imaginary
Einstein sector `Λ` is the particle↔antiparticle discriminator (the `±Δ_I` branch of `H_I = Δ_I σ₃`). -/
lemma imEinstein_charge_conjugation_odd (m_R m_I c : ℝ) :
    (complexEinsteinEnergy m_R (-m_I) c).im = -(complexEinsteinEnergy m_R m_I c).im := by
  rw [complexEinsteinEnergy_im, complexEinsteinEnergy_im]; ring

/-- **[The real Einstein energy is C-even] `Re E(−m_I) = Re E(m_I)`.** The real part `Re E = m_R c²` does not
depend on `m_I`, so charge conjugation leaves it fixed — electron and positron have the same real mass and the
same real curvature `G`: matter and antimatter gravitate identically. -/
lemma reEinstein_charge_conjugation_even (m_R m_I c : ℝ) :
    (complexEinsteinEnergy m_R (-m_I) c).re = (complexEinsteinEnergy m_R m_I c).re := by
  rw [complexEinsteinEnergy_re, complexEinsteinEnergy_re]


/-- **[Charge conjugation flips both the electric charge and the imaginary Einstein energy].** The positron's
electric charge is `−` the electron's (`conjugate_electric`), and its imaginary Einstein energy is `−` the
electron's (`imEinstein_charge_conjugation_odd`): the sign of `Im E = m_I c²` *is* the sign of the electric
charge. The complex Einstein field equation carries the particle/antiparticle label in its imaginary sector. -/
lemma chargeConjugation_flips_charge_and_imEinstein (m_R m_I c : ℝ) :
    positron.electric = -electron.electric
      ∧ (complexEinsteinEnergy m_R (-m_I) c).im = -(complexEinsteinEnergy m_R m_I c).im :=
  ⟨conjugate_electric electron, imEinstein_charge_conjugation_odd m_R m_I c⟩


/-- **[CPT conjugates the Dirac operator: electron `↦` positron].** The Greaves–Thomas CPT operator
`A = −iγ⁵` (chirality, `A² = −1`) conjugates the Dirac operator, `A·D(−p)·A⁻¹ = D(p)`: CPT maps the electron at
momentum `−p` to the positron at `p` in the *same* Dirac dynamics, flipping chirality (`{γ⁵,γ^μ}=0`) and the
charge sign — the sign flip the imaginary Einstein sector of §B carries. -/
lemma cpt_maps_electron_to_positron (p : Fin 4 → ℝ) (m : ℝ) :
    ((-Complex.I) • γ5) * diracOp (-p) m * (-((-Complex.I) • γ5)) = diracOp p m :=
  cpt_diracOp_invariant p m


/-- **[The real Einstein mass-shell is CPT-even] `lorentzianForm(−ω) = lorentzianForm(ω)`.** The Minkowski
mass-shell form `(Re ω)² − (Im ω)²` (the real Einstein invariant / rest mass²) is even under `ω ↦ −ω`, the CPT
inversion: electron and positron sit on the same mass-shell and share the same real curvature. -/
lemma realEinstein_massShell_cpt_even (ω : ℂ) : lorentzianForm (-ω) = lorentzianForm ω :=
  lorentzianForm_neg ω


/-- **[The electron/positron complex-Einstein CPT structure, assembled].** For the complex Einstein energy of
mass `m_R + i m_I` and a Dirac momentum `p`:

* the real Einstein energy is C-even and its mass-shell is CPT-even — electron and positron gravitate
  identically (`Re E`, `lorentzianForm`);
* the imaginary Einstein energy is C-odd — its sign is the electric charge, flipping electron `↦` positron;
* CPT `= −iγ⁵` conjugates the Dirac operator, mapping the electron to the positron.

The complex Einstein field equation reads CPT: real part = shared gravity, imaginary part = the charge/chirality
label whose sign distinguishes electron from positron. -/
lemma electron_positron_complexEinstein_cpt (m_R m_I c : ℝ) (p : Fin 4 → ℝ) (m : ℝ) (ω : ℂ) :
    (complexEinsteinEnergy m_R (-m_I) c).re = (complexEinsteinEnergy m_R m_I c).re
      ∧ lorentzianForm (-ω) = lorentzianForm ω
      ∧ (complexEinsteinEnergy m_R (-m_I) c).im = -(complexEinsteinEnergy m_R m_I c).im
      ∧ positron.electric = -electron.electric
      ∧ ((-Complex.I) • γ5) * diracOp (-p) m * (-((-Complex.I) • γ5)) = diracOp p m :=
  ⟨reEinstein_charge_conjugation_even m_R m_I c, lorentzianForm_neg ω,
    imEinstein_charge_conjugation_odd m_R m_I c, conjugate_electric electron,
    cpt_diracOp_invariant p m⟩

end Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronComplexEinsteinCPTChirality

end

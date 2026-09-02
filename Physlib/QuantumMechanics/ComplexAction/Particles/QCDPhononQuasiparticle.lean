/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist
public import Physlib.QuantumMechanics.ComplexAction.Bogoliubov.BosonicBogoliubovDiagonalization
meta import Zil

/-!
# The QCD superfluid phonon: a gapless bosonic quasiparticle, like the gluon

The strong-interaction analogue of the lattice phonon is the **CFL superfluid phonon** of dense (colour–
flavour-locked) quark matter: the **Nambu–Goldstone boson** of spontaneously broken baryon number `U(1)_B`.
Like the gluon it is a **gapless bosonic** excitation with **linear dispersion** `ω = v|k|` — but where the
gluon is a fundamental gauge boson propagating at `v = c = 1`, the phonon is a *composite collective*
quasiparticle propagating at the conformal sound speed `v = c_s = 1/√3 < 1` (`c_s² = ∂p/∂ε = 1/3` for the
ultrarelativistic / conformal equation of state `p = ε/3`).

* **§A — the phonon as a gapless Bogoliubov quasiparticle.** Reusing `Bogoliubov.BosonicBogoliubovDiagonalization`: the
  bosonic Bogoliubov frequency `ξ = √(h²−k²)` is gapless exactly when the pairing saturates (`k² = h²`) — the
  Goldstone/phonon point (`phonon_bogoliubov_gapless_iff`).
* **§B — the conformal sound speed.** `conformalPressure ε = ε/3`; `c_s² = 1/3` (`cflSoundSpeed_sq`) and the
  phonon is **subluminal/causal** `c_s < 1` (`cflSoundSpeed_subluminal`).
* **§C — the linear acoustic dispersion.** `phononDispersion c_s k = c_s|k|`, **gapless** at `k=0`
  (`phonon_gapless`, the massless Goldstone) with group speed `c_s` (`phonon_group_speed`).
* **§D — bosonic statistics and the gluon contrast.** The phonon (spin-0 scalar Goldstone) is a **boson**
  (`phonon_boson`, `ribbonTwist 0 = 1`), not a fermion (`phonon_not_fermion`); `cfl_phonon_quasiparticle`
  bundles gapless ∧ bosonic ∧ `c_s²=1/3` ∧ subluminal, and `phonon_gluon_linear_dispersion` shows both are
  gapless bosons with linear dispersion `ω = v|k|` (gluon `v=1`, phonon `v=c_s<1`).

**Honest layering.** Proven: the gapless condition of the bosonic Bogoliubov quasiparticle, the conformal
sound speed `c_s²=1/3` and its subluminality, the gapless linear acoustic dispersion and its group speed, and
the bosonic exchange phase (reusing `Hopf.ChargeConjugationRibbonTwist`). The microscopic CFL Lagrangian, the
Goldstone theorem itself, and the full Bogoliubov–de-Gennes spectrum `ω(k)=√(ε_k(ε_k+2gn))` are not derived;
the phonon's defining features (gapless, linear, bosonic, subluminal) are isolated.

## References

* D. T. Son, M. A. Stephanov, *Inverse meson mass ordering in colour-flavour-locking phase of high density
  QCD*, Phys. Rev. D **61** (2000) 074012, doi:10.1103/PhysRevD.61.074012; R. D. Pisarski; the CFL superfluid
  phonon `c_s = 1/√3`. `Physlib` (`Bogoliubov.BosonicBogoliubovDiagonalization`, `Hopf.ChargeConjugationRibbonTwist`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.BosonicBogoliubovDiagonalization

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Particles.QCDPhononQuasiparticle


/-- **[The phonon is the gapless Bogoliubov quasiparticle]** the bosonic Bogoliubov frequency
`ξ = √(h²−k²)` (`Bogoliubov.BosonicBogoliubovDiagonalization.diagonalizedFrequency`) vanishes — the excitation is
**gapless**, a Goldstone phonon — exactly when the pairing saturates `k² = h²`. -/
lemma phonon_bogoliubov_gapless_iff (h k : ℝ) (hk : |k| ≤ h) :
    diagonalizedFrequency h k = 0 ↔ k ^ 2 = h ^ 2 := by
  rw [← sq_eq_zero_iff, diagonalizedFrequency_sq h k hk]
  constructor <;> intro <;> linarith


/-- The **conformal (ultrarelativistic) equation of state** `p = ε/3`. -/
noncomputable def conformalPressure (ε : ℝ) : ℝ := ε / 3

/-- The **CFL phonon sound speed** `c_s = 1/√3`. -/
noncomputable def cflSoundSpeed : ℝ := Real.sqrt (1 / 3)

/-- **[Conformal sound speed squared]** `c_s² = 1/3` — the slope `∂p/∂ε` of the conformal equation of state
`p = ε/3`. -/
lemma cflSoundSpeed_sq : cflSoundSpeed ^ 2 = 1 / 3 := by
  rw [cflSoundSpeed, Real.sq_sqrt]; norm_num

/-- **[The conformal pressure has slope `c_s²`]** `p(ε) = c_s²·ε` with `c_s² = 1/3`. -/
lemma conformalPressure_slope (ε : ℝ) : conformalPressure ε = (1 / 3 : ℝ) * ε := by
  rw [conformalPressure]; ring

/-- **[The phonon is subluminal / causal]** `c_s = 1/√3 < 1` — the superfluid sound speed is below the speed
of light. -/
lemma cflSoundSpeed_subluminal : cflSoundSpeed < 1 := by
  have h : Real.sqrt (1 / 3) < Real.sqrt 1 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rwa [Real.sqrt_one] at h


/-- The **acoustic (phonon) dispersion** `ω(k) = v|k|` of a gapless bosonic quasiparticle propagating at
speed `v`. -/
def phononDispersion (v k : ℝ) : ℝ := v * |k|

/-- **[The phonon is gapless]** `ω(0) = 0` — a massless Nambu–Goldstone mode (no energy gap). -/
lemma phonon_gapless (v : ℝ) : phononDispersion v 0 = 0 := by
  rw [phononDispersion, abs_zero, mul_zero]

/-- **[The phonon group speed is `v`]** `ω(k)/|k| = v` for `k ≠ 0` — the linear dispersion propagates at the
sound speed. -/
lemma phonon_group_speed (v k : ℝ) (hk : k ≠ 0) : phononDispersion v k / |k| = v := by
  rw [phononDispersion, mul_div_assoc, div_self (abs_ne_zero.mpr hk), mul_one]

/-- The **CFL superfluid phonon dispersion** `ω(k) = c_s|k|`, `c_s = 1/√3`. -/
noncomputable def cflPhonon (k : ℝ) : ℝ := phononDispersion cflSoundSpeed k

/-- **[The CFL phonon is gapless]** `ω(0) = 0` — the Goldstone boson of broken `U(1)_B`. -/
lemma cflPhonon_gapless : cflPhonon 0 = 0 := phonon_gapless cflSoundSpeed


/-- **[The phonon is a boson]** `θ(0) = +1` — a spin-`0` scalar Goldstone has the symmetric (Bose) exchange
phase (`ribbonTwist_boson`). -/
lemma phonon_boson : ribbonTwist 0 = 1 := by simpa using ribbonTwist_boson 0

/-- **[The phonon is not a fermion]** `θ(0) = +1 ≠ −1 = θ(½)`. -/
lemma phonon_not_fermion : ribbonTwist 0 ≠ ribbonTwist (1 / 2) := by
  rw [phonon_boson, ribbonTwist_fermion]; norm_num

/-- **[The CFL superfluid phonon]** the QCD quasiparticle assembled: **gapless** (Goldstone of `U(1)_B`,
`ω(0)=0`), **bosonic** (`θ(0)=+1`), with **conformal sound speed** `c_s²=1/3` and **subluminal** propagation
`c_s<1`. The strong-interaction analogue of the lattice phonon. -/
lemma cfl_phonon_quasiparticle :
    cflPhonon 0 = 0
      ∧ ribbonTwist 0 = 1
      ∧ cflSoundSpeed ^ 2 = 1 / 3
      ∧ cflSoundSpeed < 1 :=
  ⟨cflPhonon_gapless, phonon_boson, cflSoundSpeed_sq, cflSoundSpeed_subluminal⟩

/-- **[Phonon and gluon: gapless bosons with linear dispersion]** both are gapless (`ω(0)=0`) bosonic
(`θ(0)=+1`) excitations with linear dispersion `ω = v|k|` — the gluon at the light speed `v = 1` (a
fundamental gauge boson), the CFL phonon at the subluminal sound speed `v = c_s` (a composite Goldstone
collective mode). -/
lemma phonon_gluon_linear_dispersion :
    phononDispersion 1 0 = 0 ∧ cflPhonon 0 = 0 ∧ ribbonTwist 0 = 1 ∧ cflSoundSpeed < 1 :=
  ⟨phonon_gapless 1, cflPhonon_gapless, phonon_boson, cflSoundSpeed_subluminal⟩

end Physlib.QuantumMechanics.ComplexAction.Particles.QCDPhononQuasiparticle

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.QCDPhononQuasiparticle.cflSoundSpeed_sq where
  formalizes @ "claim:the-cfl-superfluid-phonon-propagates-at-the-conformal-sound-speed-c-s-squared-equals-one-third",
  supported_by @ "paper:son-stephanov-inverse-meson-mass-ordering-colour-flavour-locking-phys-rev-d-61-074012"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.QCDPhononQuasiparticle.phonon_bogoliubov_gapless_iff where
  formalizes @ "claim:the-bosonic-bogoliubov-quasiparticle-frequency-is-gapless-exactly-when-the-pairing-saturates-the-goldstone-phonon-point",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Bogoliubov.BosonicBogoliubovDiagonalization.diagonalizedFrequency_sq"

zil attach Physlib.QuantumMechanics.ComplexAction.Particles.QCDPhononQuasiparticle.cfl_phonon_quasiparticle where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Particles.QCDPhononQuasiparticle.cflSoundSpeed_sq",
  formalizes @ "claim:the-cfl-superfluid-phonon-is-a-gapless-bosonic-quasiparticle-with-conformal-sound-speed-one-third-and-subluminal-propagation-like-the-gluon",
  requires @ "claim:the-cfl-superfluid-phonon-propagates-at-the-conformal-sound-speed-c-s-squared-equals-one-third"

zil_file_contract physlib.qcdPhononQuasiparticle where
  promises "The QCD strong-interaction analogue of the lattice phonon: the colour-flavour-locked superfluid phonon, the Nambu-Goldstone boson of spontaneously broken baryon number U(1)_B in dense quark matter. Like the gluon it is a gapless bosonic excitation with linear dispersion omega = v|k|, but where the gluon is a fundamental gauge boson at v = c = 1 the phonon is a composite collective mode at the conformal sound speed v = c_s = 1/sqrt(3) < 1 (c_s^2 = dp/de = 1/3 for the ultrarelativistic p = e/3 equation of state). Proven: the gapless condition of the bosonic Bogoliubov quasiparticle at pairing saturation, the conformal sound speed c_s^2 = 1/3 and its subluminality, the gapless linear acoustic dispersion and its group speed, and the bosonic exchange phase; the microscopic CFL Lagrangian, the Goldstone theorem, and the full Bogoliubov-de-Gennes spectrum are not derived."
  at_level physical_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.Particles.QCDPhononQuasiparticle.cflSoundSpeed",
    "lean:Physlib.QuantumMechanics.ComplexAction.Particles.QCDPhononQuasiparticle.phononDispersion",
    "lean:Physlib.QuantumMechanics.ComplexAction.Bogoliubov.BosonicBogoliubovDiagonalization.diagonalizedFrequency_sq"]
  forbids_substitutes ["a light-speed excitation, whereas the phonon is subluminal at the conformal sound speed",
    "a gapped quasiparticle, whereas the Goldstone phonon is gapless at zero momentum"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.Particles.QCDPhononQuasiparticle.cflSoundSpeed_sq,
    Physlib.QuantumMechanics.ComplexAction.Particles.QCDPhononQuasiparticle.cflSoundSpeed_subluminal,
    Physlib.QuantumMechanics.ComplexAction.Particles.QCDPhononQuasiparticle.phonon_bogoliubov_gapless_iff,
    Physlib.QuantumMechanics.ComplexAction.Particles.QCDPhononQuasiparticle.phonon_group_speed,
    Physlib.QuantumMechanics.ComplexAction.Particles.QCDPhononQuasiparticle.cfl_phonon_quasiparticle,
    Physlib.QuantumMechanics.ComplexAction.Particles.QCDPhononQuasiparticle.phonon_gluon_linear_dispersion]

/- ZIL-END -/

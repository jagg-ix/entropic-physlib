/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Hopf.DualSphereSobolevPerfectSquare

/-!
# Vorticity as a coadjoint orbit: the enstrophy Casimir and its NS dissipation

Ports the genuine, **mathematical kernel** of the Navier–Stokes *vorticity coadjoint* file
(`NSVorticityCoadjointBridge`, Arnold's geometric fluid mechanics). The source file is *not* portable: it
`axiom`-atizes the Lie bracket (`nsLieBracket`, `nsLieBracket_antisymm`) and the enstrophy dissipation
(`enstrophy_dissipation_ns`), records an unproved Euler-Casimir marker, proves `:= rfl`
identities over `ℝ`-stub presheaves, and carries a `Bool`-valued registry. What is genuine
and exact:

* **the Lie–Poisson self-bracket vanishes**: an antisymmetric bracket `{F, G} = −{G, F}` satisfies
  `{F, F} = 0` (`poissonSelf_eq_zero`) — the Hamiltonian Poisson-commutes with itself, the energy is
  conserved along its own coadjoint flow;
* **the enstrophy is a Casimir for ideal Euler, dissipating for NS**: the enstrophy rate is
  `dΩ/dt = −2ν·palin` with `palin = ∫|∇ω|² ≥ 0` the palinstrophy (`enstrophyDissipationRate`). At `ν = 0` (ideal
  Euler) it is `0` — enstrophy is conserved on the coadjoint orbit (`enstrophyDissipationRate_euler`);
  for `ν > 0` (NS) it is `≤ 0` (`enstrophyDissipationRate_nonpos`), zero **iff** the palinstrophy vanishes
  (`enstrophyDissipationRate_eq_zero_iff`) — the orbit drifts monotonically to lower-enstrophy orbits;
* **entropic time is orbit traversal**: `τ = (ν/ħ)·∫Ω` (`orbitTraversal`) is non-negative and monotone in
  the integrated enstrophy (`orbitTraversal_mono`) — higher entropic time = deeper into the low-enstrophy
  region of `𝔤*`.

* **§A — the Lie–Poisson self-bracket** (`poissonSelf_eq_zero`).
* **§B — the enstrophy Casimir / NS dissipation** (`enstrophyDissipationRate`,
  `enstrophyDissipationRate_euler`, `enstrophyDissipationRate_nonpos`,
  `enstrophyDissipationRate_eq_zero_iff`).
* **§C — entropic time as orbit traversal** (`orbitTraversal`, `orbitTraversal_nonneg`,
  `orbitTraversal_mono`, `vorticity_coadjoint_enstrophy`).

## References

* V. I. Arnold, *Ann. Inst. Fourier* 16 (1966) 319 (Euler = geodesics on `SDiff`, vorticity coadjoint
  orbits, enstrophy Casimir). Source (kernel only; axioms + `True` + `rfl`-stubs + `Bool` records):
  `NavierStokes/NSVorticityCoadjointBridge.lean`. Physical analogue: the enstrophy non-increase is the
  second-law / perfect-square monotonicity of `Hopf.DualSphereSobolevPerfectSquare`.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.NavierStokes.VorticityCoadjointEnstrophy


/-- **[Antisymmetry ⟹ self-bracket zero] `{F, F} = 0`.** A Lie–Poisson bracket that is antisymmetric
(`{F, G} = −{G, F}`) vanishes on the diagonal: the Hamiltonian Poisson-commutes with itself, so the energy
is conserved along its own coadjoint flow. (The source axiomatizes the bracket; here antisymmetry is a
hypothesis and the self-vanishing is proved.) -/
lemma poissonSelf_eq_zero {α : Type*} (P : α → α → ℝ) (h : ∀ F G, P F G = -P G F) (F : α) :
    P F F = 0 := by
  have hd := h F F; linarith


/-- **The enstrophy dissipation rate** `dΩ/dt = −2ν·palin` — the rate of change of the enstrophy
`Ω = ∫|ω|²` along an NS trajectory, with `palin = ∫|∇ω|²` the palinstrophy. -/
def enstrophyDissipationRate (ν palin : ℝ) : ℝ := -2 * ν * palin

/-- **[Ideal Euler: enstrophy is a Casimir] `dΩ/dt = 0` at `ν = 0`.** With no viscosity the enstrophy is
conserved — a Casimir constant on the coadjoint orbit (Arnold). -/
lemma enstrophyDissipationRate_euler (palin : ℝ) : enstrophyDissipationRate 0 palin = 0 := by
  unfold enstrophyDissipationRate; ring

/-- **[NS: enstrophy is non-increasing] `dΩ/dt ≤ 0`.** For `ν ≥ 0` and non-negative palinstrophy the
enstrophy dissipation rate is non-positive — the vorticity drifts to lower-enstrophy coadjoint orbits. -/
lemma enstrophyDissipationRate_nonpos (ν palin : ℝ) (hν : 0 ≤ ν) (hpalin : 0 ≤ palin) :
    enstrophyDissipationRate ν palin ≤ 0 := by
  unfold enstrophyDissipationRate; nlinarith [mul_nonneg hν hpalin]

/-- **[Stationary iff no palinstrophy] `dΩ/dt = 0 ⟺ palin = 0`** (for `ν > 0`). The enstrophy is stationary
exactly when the palinstrophy vanishes. -/
lemma enstrophyDissipationRate_eq_zero_iff (ν palin : ℝ) (hν : 0 < ν) :
    enstrophyDissipationRate ν palin = 0 ↔ palin = 0 := by
  unfold enstrophyDissipationRate
  have hlt : -2 * ν < 0 := by linarith
  constructor
  · intro h; exact (mul_eq_zero.mp h).resolve_left hlt.ne
  · intro h; rw [h]; ring


/-- **Entropic time as orbit traversal** `τ = (ν/ħ)·∫Ω` — the integrated enstrophy (in units of `ν/ħ`)
measuring how far the trajectory has traversed the foliation of coadjoint orbits. -/
noncomputable def orbitTraversal (ν ħ I : ℝ) : ℝ := (ν / ħ) * I

/-- **[Entropic time is non-negative] `τ ≥ 0`** for `ν ≥ 0`, `ħ > 0`, and non-negative integrated
enstrophy. -/
lemma orbitTraversal_nonneg (ν ħ I : ℝ) (hν : 0 ≤ ν) (hħ : 0 < ħ) (hI : 0 ≤ I) :
    0 ≤ orbitTraversal ν ħ I :=
  mul_nonneg (div_nonneg hν hħ.le) hI

/-- **[Entropic time is monotone in the integrated enstrophy].** More integrated enstrophy ⟹ more entropic
time — deeper into the low-enstrophy region of `𝔤*`. -/
lemma orbitTraversal_mono (ν ħ I₁ I₂ : ℝ) (hν : 0 ≤ ν) (hħ : 0 < ħ) (h : I₁ ≤ I₂) :
    orbitTraversal ν ħ I₁ ≤ orbitTraversal ν ħ I₂ :=
  mul_le_mul_of_nonneg_left h (div_nonneg hν hħ.le)

/-- **[Vorticity coadjoint orbit, assembled].** The enstrophy is a Casimir for ideal Euler
(`dΩ/dt = 0` at `ν = 0`) and dissipates for NS (`dΩ/dt = −2ν·palin ≤ 0`, zero iff `palin = 0`); entropic time
`τ = (ν/ħ)·∫Ω` is non-negative and monotone in the integrated enstrophy. The NS trajectory traverses the
coadjoint orbits monotonically toward lower enstrophy — the geometric face of the entropic-time arrow. -/
lemma vorticity_coadjoint_enstrophy (ν palin ħ I₁ I₂ : ℝ) (hν : 0 < ν) (hpalin : 0 ≤ palin) (hħ : 0 < ħ)
    (hI : 0 ≤ I₁) (hmono : I₁ ≤ I₂) :
    enstrophyDissipationRate 0 palin = 0
      ∧ enstrophyDissipationRate ν palin ≤ 0
      ∧ (enstrophyDissipationRate ν palin = 0 ↔ palin = 0)
      ∧ 0 ≤ orbitTraversal ν ħ I₁
      ∧ orbitTraversal ν ħ I₁ ≤ orbitTraversal ν ħ I₂ :=
  ⟨enstrophyDissipationRate_euler palin, enstrophyDissipationRate_nonpos ν palin hν.le hpalin,
    enstrophyDissipationRate_eq_zero_iff ν palin hν, orbitTraversal_nonneg ν ħ I₁ hν.le hħ hI,
    orbitTraversal_mono ν ħ I₁ I₂ hν.le hħ hmono⟩

end Physlib.QuantumMechanics.ComplexAction.NavierStokes.VorticityCoadjointEnstrophy

end

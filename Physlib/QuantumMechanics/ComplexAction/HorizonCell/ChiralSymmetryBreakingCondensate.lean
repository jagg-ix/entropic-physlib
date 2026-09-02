/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.PolyakovLoopDeconfinement
public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.QCDQuarkMassRunning
public import Mathlib.Analysis.Calculus.MeanValue
public import Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation
meta import Zil

/-!
# Chiral symmetry breaking: the condensate `⟨q̄q⟩` as order parameter, the pion as Goldstone (GMOR)

The second pillar of non-perturbative QCD, alongside confinement: **spontaneous chiral symmetry breaking**. The
axial `U(1)_A` chiral rotation `q ↦ e^{iαγ⁵}q` acts on the scalar/pseudoscalar bilinears
`(σ, π) = (⟨q̄q⟩, ⟨q̄ iγ⁵ q⟩)` as an `O(2)` rotation of the "chiral circle"; the chiral condensate `⟨q̄q⟩ ≠ 0` is
its order parameter, and the pion is the (pseudo-)Goldstone boson of the broken symmetry.

Structurally this is the exact partner of the deconfinement order parameter (`PolyakovLoopDeconfinement`):

* the **chiral rotation preserves the condensate radius** `σ² + π²` (`chiralRotate_preserves_radius`), so a
  chirally-invariant potential is flat along the rotation orbit — the **massless Goldstone (pion) direction**;
* an order parameter **invariant under a nontrivial chiral rotation is forced to zero**
  (`chiral_invariant_forces_zero`), exactly as `center_invariant_forces_zero` forces the Polyakov loop to vanish
  in the confined phase: `⟨q̄q⟩ = 0` is the chirally-*restored* (symmetric) phase, `⟨q̄q⟩ ≠ 0` is broken;
* a nonzero condensate **breaks the chiral symmetry** (`condensate_breaks_chiral`) — a chiral rotation moves it,
  the vacuum picks a direction;
* the **Gell-Mann–Oakes–Renner relation** `m_π² f_π² = −2 m_q ⟨q̄q⟩` (`gmorPionMassSq`) gives the pion its mass
  from the *explicit* breaking by the quark mass `m_q` (`QCDQuarkMassRunning`): the pion is **massless in the
  chiral limit** `m_q → 0` (`gmor_chiral_limit`) and `m_π² > 0` for a physical (negative) condensate
  (`gmor_pos`).

So QCD has two order parameters with one structure: the Polyakov loop `⟨L⟩` (center `Z(3)`, deconfinement) and
the chiral condensate `⟨q̄q⟩` (axial `U(1)`, chiral restoration), each vanishing exactly in its symmetric phase
(`two_qcd_order_parameters`).

* **§A — the chiral rotation and its invariant radius** (`chiralRotate`, `chiralRotate_preserves_radius`).
* **§B — invariance forces the condensate to zero** (`chiral_invariant_forces_zero`).
* **§C — a nonzero condensate breaks chiral symmetry** (`condensate_breaks_chiral`).
* **§D — GMOR: the pion mass from the quark mass** (`gmorPionMassSq`, `gmor_chiral_limit`, `gmor_pos`).
* **§E — the two QCD order parameters** (`two_qcd_order_parameters`).

**Honest layering.** The chiral rotation is the exact `O(2)` action, its radius invariance and the
invariance-forces-zero / symmetry-breaking facts are exact algebra; GMOR is recorded as the exact relation
`m_π² = −2 m_q ⟨q̄q⟩/f_π²` with its chiral-limit and positivity, not derived from the effective Lagrangian. No
finite-`T` condensate melting curve or `T_c` is constructed. ## References

* M. Gell-Mann, R.J. Oakes, B. Renner (GMOR); Nambu–Jona-Lasinio (chiral condensate as order parameter). Repo
  carriers: `HorizonCell.PolyakovLoopDeconfinement`, `HorizonCell.QCDQuarkMassRunning`.


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.HorizonCell.PolyakovLoopDeconfinement
open Physlib.QuantumMechanics.ComplexAction.Particles.NeutrinoModel

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.HorizonCell.ChiralSymmetryBreakingCondensate


/-- **The axial chiral rotation on the bilinears** `(σ, π) = (⟨q̄q⟩, ⟨q̄ iγ⁵ q⟩)` — the `U(1)_A` rotation
`q ↦ e^{iαγ⁵}q` acts as an `O(2)` rotation of the chiral circle. -/
noncomputable def chiralRotate (a : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  (Real.cos a * v.1 - Real.sin a * v.2, Real.sin a * v.1 + Real.cos a * v.2)

/-- **[The chiral rotation preserves the condensate radius] `σ² + π²` invariant.** The axial rotation is an
isometry of the chiral circle: `|⟨q̄q⟩|² + |⟨q̄iγ⁵q⟩|²` is conserved. A potential depending only on this radius is
flat along the orbit — the massless pion (Goldstone) direction. -/
lemma chiralRotate_preserves_radius (a : ℝ) (v : ℝ × ℝ) :
    (chiralRotate a v).1 ^ 2 + (chiralRotate a v).2 ^ 2 = v.1 ^ 2 + v.2 ^ 2 := by
  unfold chiralRotate
  simp only []
  linear_combination (v.1 ^ 2 + v.2 ^ 2) * Real.sin_sq_add_cos_sq a


/-- **[A condensate invariant under a nontrivial chiral rotation vanishes] `R(π/2)·v = v ⟹ v = 0`.** If the
chiral order parameter is unchanged by the quarter-turn axial rotation `R(π/2) : (σ,π) ↦ (−π, σ)` (unbroken
chiral symmetry), it must be zero — the chirally-restored phase `⟨q̄q⟩ = 0`. The exact analogue of
`center_invariant_forces_zero` for the Polyakov loop. -/
lemma chiral_invariant_forces_zero (v : ℝ × ℝ) (h : chiralRotate (Real.pi / 2) v = v) : v = 0 := by
  unfold chiralRotate at h
  rw [Real.cos_pi_div_two, Real.sin_pi_div_two] at h
  simp only [zero_mul, one_mul, zero_sub, add_zero] at h
  obtain ⟨h1, h2⟩ := Prod.ext_iff.mp h
  have hv2 : v.2 = 0 := by linarith
  have hv1 : v.1 = 0 := by linarith
  exact Prod.ext hv1 hv2


/-- **[A nonzero condensate breaks chiral symmetry] `R(a)·(⟨q̄q⟩,0) ≠ (⟨q̄q⟩,0)`.** A vacuum with a nonzero scalar
condensate and vanishing pseudoscalar is moved by any chiral rotation with `sin a ≠ 0` (it generates a
pseudoscalar component `sin a · ⟨q̄q⟩ ≠ 0`): the vacuum picks a direction on the chiral circle — spontaneous
symmetry breaking. -/
lemma condensate_breaks_chiral (qq a : ℝ) (hqq : qq ≠ 0) (ha : Real.sin a ≠ 0) :
    chiralRotate a (qq, 0) ≠ (qq, 0) := by
  intro h
  have h2 : (chiralRotate a (qq, 0)).2 = (qq, 0).2 := by rw [h]
  unfold chiralRotate at h2
  simp only [mul_zero, add_zero] at h2
  exact (mul_ne_zero ha hqq) h2


/-- **The Gell-Mann–Oakes–Renner pion mass²** `m_π² = −2 m_q ⟨q̄q⟩ / f_π²` — the pion mass generated by the
*explicit* chiral breaking of the quark mass `m_q` acting on the condensate `⟨q̄q⟩` (negative), with `f_π` the
pion decay constant. -/
noncomputable def gmorPionMassSq (m_q qq f_pi : ℝ) : ℝ := -2 * m_q * qq / f_pi ^ 2

/-- **[The pion is massless in the chiral limit] `m_q → 0 ⟹ m_π² = 0`.** With no explicit breaking the pion is an
exact Goldstone boson of spontaneous chiral symmetry breaking. -/
lemma gmor_chiral_limit (qq f_pi : ℝ) : gmorPionMassSq 0 qq f_pi = 0 := by
  unfold gmorPionMassSq; simp

/-- **[The physical pion mass² is positive] `m_q > 0, ⟨q̄q⟩ < 0 ⟹ m_π² > 0`.** With a positive quark mass and the
physical (negative) chiral condensate, GMOR gives a genuine positive pion mass² — the pseudo-Goldstone acquires
mass from the small explicit breaking `m_q` (the running quark mass of `QCDQuarkMassRunning`). -/
lemma gmor_pos (m_q qq f_pi : ℝ) (hm : 0 < m_q) (hqq : qq < 0) (hf : f_pi ≠ 0) :
    0 < gmorPionMassSq m_q qq f_pi := by
  unfold gmorPionMassSq
  apply div_pos _ (by positivity)
  nlinarith [mul_pos hm (neg_pos.mpr hqq)]

/-- **[GMOR: the pion mass² is linear in the quark mass] `m_π²(l·m_q) = l·m_π²(m_q)`.** The
Gell-Mann–Oakes–Renner mass² is exactly *linear* in the quark mass `m_q`, so `m_π² ∝ m_q` — the defining
feature of a pseudo-Goldstone boson: its mass² is first order in the explicit breaking, not `O(1)`. -/
lemma gmorPionMassSq_linear_in_quarkMass (l m_q qq f_pi : ℝ) :
    gmorPionMassSq (l * m_q) qq f_pi = l * gmorPionMassSq m_q qq f_pi := by
  unfold gmorPionMassSq; ring

/-- **[GMOR: the pion mass scales as `√(m_q)`] `m_π(l·m_q) = √l · m_π(m_q)`** for `l ≥ 0`. Since
`m_π² ∝ m_q` is linear, the pion mass itself is homogeneous of degree `1/2` in the quark mass — the
distinctive `√(m_q)` law of the pseudo-Goldstone boson (ordinary hadron masses run as `O(1) + O(m_q)`). -/
lemma gmorPionMass_sqrt_scaling (l m_q qq f_pi : ℝ) (hl : 0 ≤ l) :
    Real.sqrt (gmorPionMassSq (l * m_q) qq f_pi)
      = Real.sqrt l * Real.sqrt (gmorPionMassSq m_q qq f_pi) := by
  rw [gmorPionMassSq_linear_in_quarkMass, Real.sqrt_mul hl]


/-- **[The two QCD order parameters share one structure].** Non-perturbative QCD has two order parameters, each
vanishing exactly in its symmetric phase by the same "invariance forces zero" mechanism:

* the **chiral condensate** `⟨q̄q⟩` — invariant under the nontrivial axial rotation ⟹ zero (chirally restored),
  and the pion is massless in the chiral limit;
* the **Polyakov loop** `⟨L⟩` — invariant under the nontrivial `Z(3)` center ⟺ zero (confined).

Chiral restoration (axial `U(1)`) and deconfinement (center `Z(3)`) are the two symmetric phases of QCD, with a
common order-parameter structure. -/
lemma two_qcd_order_parameters (L : ℂ) (v : ℝ × ℝ) (qq f_pi : ℝ) :
    (chiralRotate (Real.pi / 2) v = v → v = 0)
      ∧ (L = centerTransform cubeRoot L ↔ L = 0)
      ∧ gmorPionMassSq 0 qq f_pi = 0 :=
  ⟨chiral_invariant_forces_zero v, cubeRoot_invariant_iff_confined L, gmor_chiral_limit qq f_pi⟩


/-! ## Symanzik's Euclidean proof of the Goldstone theorem

The Euclidean/analytic partner of the finite-dimensional chiral dichotomy above (Symanzik, *Euclidean
Proof of the Goldstone Theorem*, Commun. Math. Phys. 6 (1967) 228–232). The order parameter is the
`τ`-dependence of the Schwinger function `Sᵗ(x₁…xₙ)` under the symmetry automorphism `A ↦ Aᵗ`, whose
`τ`-derivative is the *current surface integral* (Eq. 6, `∂_τ Sᵗ = ∮ dOᵘ S^{μ,τ}`). When the mass
spectrum has a gap above the vacuum, the Schwinger functions have the exponential cluster property in
all directions and the surface integral vanishes as the surface is pushed to infinity — so the
symmetry is unbroken; contrapositively, a broken symmetry forces a non-vanishing surface term, hence
no mass gap, i.e. a massless Goldstone mode. -/

/-- **[Symanzik: mass gap ⟹ unbroken symmetry]** — the Euclidean master equation with a vanishing
current surface integral forces the order parameter to be `τ`-independent. If `∂_τ Sᵗ` equals the
surface term (Eq. 6) and that term vanishes for every `τ` — which the exponential cluster property
supplies when there is a mass gap above the vacuum — then `Sᵗ` is constant in `τ`: the symmetry
automorphism is unitarily implementable leaving the vacuum invariant (no symmetry breaking). -/
theorem euclidean_goldstone_unbroken_of_gap {S surf : ℝ → ℝ}
    (hmaster : ∀ τ, HasDerivAt S (surf τ) τ) (hcluster : ∀ τ, surf τ = 0) (τ₁ τ₂ : ℝ) :
    S τ₁ = S τ₂ := by
  refine is_const_of_deriv_eq_zero (fun τ => (hmaster τ).differentiableAt) ?_ τ₁ τ₂
  intro τ
  rw [(hmaster τ).deriv, hcluster τ]

/-- **[The Goldstone theorem, Euclidean/Symanzik form]** — the contrapositive. If the symmetry is
*broken* (the order-parameter Schwinger function `Sᵗ` genuinely depends on `τ`), then the current
surface integral cannot vanish for all `τ`; hence the Schwinger functions lack the exponential cluster
property, i.e. the mass spectrum has **no gap** above the vacuum — a massless Goldstone mode. -/
theorem euclidean_goldstone_massless_of_broken {S surf : ℝ → ℝ}
    (hmaster : ∀ τ, HasDerivAt S (surf τ) τ) (hbroken : ∃ τ₁ τ₂, S τ₁ ≠ S τ₂) :
    ∃ τ, surf τ ≠ 0 := by
  by_contra hcon
  simp only [not_exists, ne_eq, not_not] at hcon
  obtain ⟨τ₁, τ₂, hne⟩ := hbroken
  exact hne (euclidean_goldstone_unbroken_of_gap hmaster hcon τ₁ τ₂)

/-- **[The Euclidean Goldstone dichotomy]** — the vanishing of the current surface integral (the mass
gap / cluster property) holds for every `τ` **iff** the order-parameter Schwinger function is
`τ`-independent (unbroken symmetry). This is the exact Euclidean partner of `two_qcd_order_parameters`:
symmetry restoration ⟺ vanishing surface term, symmetry breaking ⟺ a massless Goldstone mode. -/
theorem euclidean_goldstone_dichotomy {S surf : ℝ → ℝ}
    (hmaster : ∀ τ, HasDerivAt S (surf τ) τ) :
    (∀ τ, surf τ = 0) ↔ (∀ τ₁ τ₂, S τ₁ = S τ₂) := by
  constructor
  · intro h τ₁ τ₂
    exact euclidean_goldstone_unbroken_of_gap hmaster h τ₁ τ₂
  · intro hconst τ
    have hd : deriv S τ = 0 := by
      rw [show S = fun _ => S 0 from funext fun x => hconst x 0]; simp
    rw [← (hmaster τ).deriv]; exact hd

/-! ### The Lorentzian (Wightman) form: the massless Goldstone pole on the null mass shell

The momentum-space partner of the Euclidean argument above. In Wightman theory the order parameter is
the Goldstone commutator `⟨0|[Q, A]|0⟩ = ⟨δA⟩ ≠ 0`, and the current–field commutator
`⟨0|[jᵘ(x), A(0)]|0⟩` has, by Lorentz covariance, the spectral form `σᵘ(p) = pᵘ σ(p²)`. Current
conservation `∂_μ jᵘ = 0` reads `pᵤ σᵘ(p) = p² σ(p²) = 0` in momentum space, i.e. `s · σ(s) = 0` over
the invariant mass-squared `s = p²`. Hence `σ` is supported only at `s = 0` — the null mass shell /
light cone — so the broken-symmetry mode is *massless*, with the light-cone dispersion `E = |k|`
(`bogoliubovEnergy k 0`, the gap-dispersion `√(k²+Δ²)` at zero gap `Δ = 0`). This is the exact
Lorentzian partner of `euclidean_goldstone_massless_of_broken`. -/

/-- **[The massless Goldstone dispersion]** — the broken-symmetry mode sits at zero gap `Δ = 0`, where
the Bogoliubov gap-dispersion `E = √(k² + Δ²)` collapses to the light-cone relation `E = |k|` (the null
mass shell `p² = 0`). Reuses `bogoliubovEnergy` from the BCS/Bogoliubov spectrum. -/
theorem goldstone_massless_dispersion (k : ℝ) :
    Bogoliubov.Transformation.bogoliubovEnergy k 0 = |k| := by
  unfold Bogoliubov.Transformation.bogoliubovEnergy
  rw [show (0 : ℝ) ^ 2 = 0 by norm_num, add_zero, Real.sqrt_sq_eq_abs]

/-- **[The Lorentzian Goldstone theorem]** — current conservation `p² σ(p²) = 0` forces the current–
field commutator's spectral density `σ` onto the null mass shell `s = 0`: off the shell (`s ≠ 0`) the
density vanishes, so the broken-symmetry mode carries no mass — a massless Goldstone boson. -/
theorem lorentzian_goldstone_massShell {σ : ℝ → ℝ} (hconserv : ∀ s, s * σ s = 0)
    {s : ℝ} (hs : s ≠ 0) : σ s = 0 :=
  (mul_eq_zero.mp (hconserv s)).resolve_left hs

/-- **[No massive Goldstone mode]** — the contrapositive: a nonzero off-shell spectral weight
(`σ s ≠ 0` at `s ≠ 0`, a massive mode) makes `s · σ(s) ≠ 0`, violating current conservation. A broken
continuous symmetry admits no *massive* companion of the massless Goldstone boson. -/
theorem lorentzian_no_massive_goldstone {σ : ℝ → ℝ} {s : ℝ} (hs : s ≠ 0) (hσ : σ s ≠ 0) :
    s * σ s ≠ 0 :=
  mul_ne_zero hs hσ

/-- **[Euclidean–Lorentzian Goldstone unification]** — a single spontaneously broken continuous
symmetry entails a massless mode in *both* pictures: the Euclidean position-space one (a broken order
parameter forces a non-vanishing current surface term, so the Schwinger functions have no mass gap) and
the Lorentzian momentum-space one (current conservation concentrates the spectral density on the null
mass shell `s = 0`). The position-space cluster-property failure and the momentum-space light-cone pole
are the two faces of the Goldstone theorem. -/
theorem goldstone_euclidean_lorentzian_unified {S surf σ : ℝ → ℝ}
    (hmaster : ∀ τ, HasDerivAt S (surf τ) τ) (hbroken : ∃ τ₁ τ₂, S τ₁ ≠ S τ₂)
    (hconserv : ∀ s, s * σ s = 0) :
    (∃ τ, surf τ ≠ 0) ∧ (∀ s, s ≠ 0 → σ s = 0) :=
  ⟨euclidean_goldstone_massless_of_broken hmaster hbroken,
   fun _ hs => lorentzian_goldstone_massShell hconserv hs⟩

end Physlib.QuantumMechanics.ComplexAction.HorizonCell.ChiralSymmetryBreakingCondensate

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.ChiralSymmetryBreakingCondensate.euclidean_goldstone_unbroken_of_gap where
  formalizes @ "claim:a-mass-gap-makes-the-current-surface-integral-vanish-forcing-the-order-parameter-schwinger-function-to-be-tau-independent-unbroken-symmetry",
  supported_by @ "paper:symanzik-euclidean-proof-of-the-goldstone-theorem"

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.ChiralSymmetryBreakingCondensate.euclidean_goldstone_massless_of_broken where
  formalizes @ "claim:a-broken-symmetry-forces-a-non-vanishing-current-surface-integral-hence-no-mass-gap-a-massless-goldstone-mode",
  requires @ "claim:a-mass-gap-makes-the-current-surface-integral-vanish-forcing-the-order-parameter-schwinger-function-to-be-tau-independent-unbroken-symmetry",
  supported_by @ "paper:symanzik-euclidean-proof-of-the-goldstone-theorem"

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.ChiralSymmetryBreakingCondensate.euclidean_goldstone_dichotomy where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.ChiralSymmetryBreakingCondensate.euclidean_goldstone_unbroken_of_gap",
  formalizes @ "claim:the-vanishing-of-the-current-surface-integral-holds-iff-the-order-parameter-is-tau-independent-the-euclidean-goldstone-dichotomy"

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.ChiralSymmetryBreakingCondensate.goldstone_massless_dispersion where
  formalizes @ "claim:the-broken-symmetry-mode-sits-at-zero-gap-where-the-bogoliubov-dispersion-collapses-to-the-light-cone-relation-E-equals-abs-k-the-null-mass-shell",
  supported_by @ "object:Physlib.QuantumMechanics.ComplexAction.Bogoliubov.Transformation.bogoliubovEnergy"

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.ChiralSymmetryBreakingCondensate.lorentzian_goldstone_massShell where
  formalizes @ "claim:current-conservation-p-squared-sigma-equals-zero-forces-the-current-field-commutator-spectral-density-onto-the-null-mass-shell-a-massless-goldstone-boson",
  supported_by @ "paper:goldstone-salam-weinberg-broken-symmetries-and-the-goldstone-theorem"

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.ChiralSymmetryBreakingCondensate.lorentzian_no_massive_goldstone where
  formalizes @ "claim:a-nonzero-off-shell-spectral-weight-a-massive-mode-violates-current-conservation-so-a-broken-symmetry-admits-no-massive-companion",
  requires @ "claim:current-conservation-p-squared-sigma-equals-zero-forces-the-current-field-commutator-spectral-density-onto-the-null-mass-shell-a-massless-goldstone-boson"

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.ChiralSymmetryBreakingCondensate.goldstone_euclidean_lorentzian_unified where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.ChiralSymmetryBreakingCondensate.euclidean_goldstone_massless_of_broken",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.ChiralSymmetryBreakingCondensate.lorentzian_goldstone_massShell",
  formalizes @ "claim:a-single-spontaneously-broken-continuous-symmetry-entails-a-massless-mode-in-both-the-euclidean-position-space-and-lorentzian-momentum-space-pictures",
  requires @ "claim:a-broken-symmetry-forces-a-non-vanishing-current-surface-integral-hence-no-mass-gap-a-massless-goldstone-mode",
  requires @ "claim:current-conservation-p-squared-sigma-equals-zero-forces-the-current-field-commutator-spectral-density-onto-the-null-mass-shell-a-massless-goldstone-boson"

zil attach Physlib.QuantumMechanics.ComplexAction.HorizonCell.ChiralSymmetryBreakingCondensate.gmorPionMass_sqrt_scaling where
  formalizes @ "claim:the-gmor-pion-mass-scales-as-the-square-root-of-the-quark-mass-because-the-mass-squared-is-linear-in-m-q-the-pseudo-goldstone-signature",
  supported_by @ "paper:gell-mann-oakes-renner-1968-behavior-of-current-divergences"

zil_file_contract physlib.chiralSymmetryBreakingCondensate where
  promises "Spontaneous symmetry breaking and the Goldstone theorem in three complementary forms. Finite chiral form: the axial rotation preserves the condensate radius (the flat massless pion direction), a condensate invariant under a nontrivial chiral rotation is forced to zero (chiral restoration), a nonzero condensate breaks the chiral symmetry, and the GMOR pion mass vanishes in the chiral limit. Euclidean/Symanzik form: the tau-derivative of the order-parameter Schwinger function equals the current surface integral (Eq. 6); a mass gap makes that integral vanish (exponential cluster property) so the symmetry is unbroken, and contrapositively a broken symmetry forces a non-vanishing surface term, hence no mass gap -- a massless Goldstone mode. Lorentzian/Wightman form: the current-field commutator's spectral density obeys s*sigma(s)=0 over the invariant mass-squared s=p^2 by current conservation, so it is supported only on the null mass shell s=0 (light-cone dispersion E=|k| = bogoliubovEnergy at zero gap) -- a massless Goldstone boson, with no massive companion. The unification theorem shows a single broken symmetry entails a massless mode in both the position-space (no mass gap) and momentum-space (null-shell pole) pictures. GMOR scaling: because the pion mass-squared is linear in the quark mass, the pion mass itself scales as the square root of the quark mass -- the distinctive pseudo-Goldstone signature."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.ChiralSymmetryBreakingCondensate.chiralRotate",
    "lean:Physlib.QuantumMechanics.ComplexAction.HorizonCell.ChiralSymmetryBreakingCondensate.gmorPionMassSq"]
  forbids_substitutes ["the analytic construction of Schwinger functions, the exponential cluster property, and the reconstruction theorem, which are the cited Euclidean-QFT infrastructure summarized by the vanishing-surface-term hypothesis",
    "the Kallen-Lehmann spectral representation and the Lorentz-covariance decomposition sigma^mu(p)=p^mu sigma(p^2), which are the cited Wightman infrastructure summarized by the current-conservation hypothesis s*sigma(s)=0",
    "any claim of Goldstone-mode dynamics, only the mass-gap-versus-symmetry-breaking dichotomy and the null-mass-shell spectral concentration are carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.HorizonCell.ChiralSymmetryBreakingCondensate.chiral_invariant_forces_zero,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.ChiralSymmetryBreakingCondensate.condensate_breaks_chiral,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.ChiralSymmetryBreakingCondensate.gmor_chiral_limit,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.ChiralSymmetryBreakingCondensate.gmorPionMass_sqrt_scaling,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.ChiralSymmetryBreakingCondensate.euclidean_goldstone_unbroken_of_gap,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.ChiralSymmetryBreakingCondensate.euclidean_goldstone_massless_of_broken,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.ChiralSymmetryBreakingCondensate.euclidean_goldstone_dichotomy,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.ChiralSymmetryBreakingCondensate.goldstone_massless_dispersion,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.ChiralSymmetryBreakingCondensate.lorentzian_goldstone_massShell,
    Physlib.QuantumMechanics.ComplexAction.HorizonCell.ChiralSymmetryBreakingCondensate.goldstone_euclidean_lorentzian_unified]

/- ZIL-END -/

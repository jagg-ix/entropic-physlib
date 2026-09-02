/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalyRapidity
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.TorusHilbert
public import Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.EntanglementEntropy
public import Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.WilsonLoopBraidingRibbon
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.ModularRepresentation
public import Physlib.QuantumMechanics.ComplexAction.ExchangeStatisticsSpectrum
public import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The `ν = 1/2` FQHE in wide quantum wells: one-component ↔ unentangled subbands

Formalization of the half-filling arithmetic of T. Zhao, W. N. Faugno, S. Pu, A. C. Balram, J. K. Jain,
*"Origin of the `ν = 1/2` fractional quantum Hall effect in wide quantum wells"*, Phys. Rev. B **103**, 155306
(2021), DOI:10.1103/PhysRevB.103.155306 — whose 3D fixed-phase DMC finds the observed `ν = 1/2` state to be the
**one-component** Pfaffian, not the two-component `(3,3,1)` state.

A wide quantum well has **two subbands** (symmetric `S` / antisymmetric `AS`, split by `Δ_SAS`): a bipartite
two-mode system. The paper's central dichotomy — *one-component vs two-component* — is exactly *unentangled vs
entangled between the two subbands*. This file makes that identification precise by reusing the repository's
Schmidt-defect machinery from the muon mode:

* **§A — half-filling arithmetic (genuine FQHE).** `ν = N/N_φ = 1/2 ⟺ N_φ = 2N`; the composite fermion attaches
  two flux quanta so its effective flux vanishes at half-filling (`cf_zero_flux_at_half_filling` — the CF Fermi
  sea); the Laughlin/Jastrow exponent is `m = 2` (`laughlin_two_is_half`).
* **§B — the subband-entanglement bridge (shared Schmidt kernel).** With the inter-subband entanglement described
  by a Schmidt number `K = coth η` (the same quasifree two-mode-squeezed kernel as the muon mode), the
  **component defect** `K² − 1` measures the two-componentness: `K = 1` (no inter-subband entanglement) is the
  *one-component* state — the paper's `ν=1/2` answer — with effective `g = 2` (Dirac-like); `K > 1` is genuinely
  two-component. Via `gFactor_eq_two_schmidt_sq` and `anomaly_eq_schmidt_sq_sub_one` the law `g = 2K²` and
  the defect `K² − 1 = csch²η` are *literally the muon-mode invariants*, instantiated for the `S`/`AS`
  bipartition.

**Honest layering.** §A is the paper's exact `ν=1/2` physics. §B is a *structural* identification — the
one-component / two-component dichotomy ↔ the `K=1` / `K>1` Schmidt limit, using the shared quasifree kernel — not a
derivation of the DMC energetics; it reuses the muon theorems to express *which* entanglement content
distinguishes the candidate states.

## References

* T. Zhao et al., Phys. Rev. B 103, 155306 (2021), DOI:10.1103/PhysRevB.103.155306 — Sec. I–II, Fig. 3.
* `Physlib` (`MuonAnomaly.AnomalyRapidity` — `gFactor_eq_two_schmidt_sq`, `anomaly_eq_schmidt_sq_sub_one`;
  `MuonAnomaly.SchmidtRapidityHyperbolicUnification`).


-/

set_option autoImplicit false

open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.AnomalyRapidity
open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.AnomalousMagneticMoment
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.EntanglementEntropy
open Physlib.QuantumMechanics.ComplexAction.Hopf.ChargeConjugationRibbonTwist
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.WilsonLoopBraidingRibbon
open Physlib.QuantumMechanics.ComplexAction.ExchangeStatisticsSpectrum

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.FractionalQuantumHallHalfFilling


/-- The **Landau-level filling factor** `ν = N / N_φ` (electrons per flux quantum). -/
noncomputable def fillingFactor (N Nφ : ℝ) : ℝ := N / Nφ

/-- **[Half-filling]** `ν = 1/2 ⟺ N_φ = 2N` — the half-filled Landau level studied in the paper. -/
lemma half_filling_iff_flux (N Nφ : ℝ) (hNφ : Nφ ≠ 0) :
    fillingFactor N Nφ = 1 / 2 ↔ Nφ = 2 * N := by
  rw [fillingFactor, div_eq_div_iff hNφ (two_ne_zero)]
  constructor <;> intro h <;> linarith

/-- The composite-fermion **effective flux** `N_φ* = N_φ − 2p·N` after attaching `2p` vortices. -/
noncomputable def cfEffectiveFlux (Nφ N p : ℝ) : ℝ := Nφ - 2 * p * N

/-- **[The composite-fermion Fermi sea]** at half-filling (`N_φ = 2N`) the `p = 1` composite fermion (two
attached flux quanta) sees **zero** effective flux — the gapless CF Fermi sea, one of the two `ν=1/2`
candidates. -/
lemma cf_zero_flux_at_half_filling (Nφ N : ℝ) :
    cfEffectiveFlux Nφ N 1 = 0 ↔ Nφ = 2 * N := by
  unfold cfEffectiveFlux; constructor <;> intro h <;> linarith

/-- The **Laughlin / Jastrow filling** `ν = 1/m` (the wavefunction `∏(z_i − z_j)^m`). -/
noncomputable def laughlinFilling (m : ℝ) : ℝ := 1 / m

/-- **[`ν = 1/2` is the `m = 2` Jastrow factor]** the half-filled state has the exponent-2 Jastrow
correlations. -/
lemma laughlin_two_is_half : laughlinFilling 2 = 1 / 2 := by unfold laughlinFilling; norm_num

/-!

The paper's `ν=1/2` is not an isolated fraction: it is the `n → ∞` limit of the **Jain sequence**
`ν_n = n/(2pn+1)` (`p` vortices-pairs attached, `n` the integer composite-fermion filling). This block
generalizes §A so that the special status of half-filling is *derived*: the Laughlin primary fractions sit at
`n = 1` (odd denominator, incompressible), while the half-filled limit `n → ∞` has even denominator `2p` — so
no fermionic Laughlin state exists there, which is exactly why the paper must compare the **Pfaffian** and the
**composite-fermion Fermi sea**. -/

/-- The **Jain sequence** filling `ν = n/(2pn+1)` — `n` composite-fermion Landau levels with `2p` attached flux
quanta. -/
noncomputable def jainFilling (n p : ℝ) : ℝ := n / (2 * p * n + 1)

/-- **[The composite-fermion flux-attachment law] `1/ν = 2p + 1/ν*`** — the inverse electron filling is `2p`
(the attached flux) plus the inverse composite-fermion filling `1/n`. This is the defining relation of the CF
construction; everything in §A is a special case. -/
lemma inv_jainFilling (n p : ℝ) (hn : n ≠ 0) :
    (jainFilling n p)⁻¹ = 2 * p + 1 / n := by
  rw [jainFilling, inv_div]; field_simp

/-- **[Half-filling is the `n → ∞` limit]** `1/ν − 2p = 1/n` — the deviation of the inverse filling from the
even denominator `2p` is exactly `1/n`, vanishing as the composite-fermion filling `n → ∞`. For `p = 1` this is
the approach `ν → 1/2`: the gapless composite-fermion Fermi sea. -/
lemma inv_jainFilling_sub_half (n p : ℝ) (hn : n ≠ 0) :
    (jainFilling n p)⁻¹ - 2 * p = 1 / n := by rw [inv_jainFilling n p hn]; ring

/-- **[The Jain sequence converges to half-filling] `ν_n → 1/(2p)` as `n → ∞`** — the rigorous limit: the
composite-fermion sequence `n/(2pn+1)` tends to the even-denominator filling `1/(2p)` (for `p=1`, `ν=1/2`), the
gapless composite-fermion Fermi sea that the Pfaffian competes with. -/
lemma jainFilling_tendsto_half (p : ℝ) (hp : p ≠ 0) :
    Filter.Tendsto (fun n : ℝ => jainFilling n p) Filter.atTop (nhds ((2 * p)⁻¹)) := by
  have key : (fun n : ℝ => jainFilling n p) =ᶠ[Filter.atTop] fun n : ℝ => (2 * p + 1 / n)⁻¹ := by
    filter_upwards [Filter.eventually_ne_atTop (0 : ℝ)] with n hn
    rw [← inv_jainFilling n p hn, inv_inv]
  rw [Filter.tendsto_congr' key]
  have h1 : Filter.Tendsto (fun n : ℝ => 1 / n) Filter.atTop (nhds 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero
  have h0 : Filter.Tendsto (fun n : ℝ => 2 * p + 1 / n) Filter.atTop (nhds (2 * p)) := by
    simpa using Filter.Tendsto.const_add (2 * p) h1
  exact h0.inv₀ (mul_ne_zero two_ne_zero hp)

/-- **[The `n = 1` endpoint is the Laughlin fraction]** `ν₁ = 1/(2p+1)` — the Jain sequence begins at the
incompressible Laughlin/primary fraction with **odd** denominator `2p+1`. -/
lemma jain_primary_is_laughlin (p : ℝ) : jainFilling 1 p = laughlinFilling (2 * p + 1) := by
  rw [jainFilling, laughlinFilling]; ring

/-- **[`ν = 1/3` is the first Jain/Laughlin state]** `jainFilling 1 1 = 1/3`. -/
lemma jain_one_one_third : jainFilling 1 1 = 1 / 3 := by rw [jainFilling]; norm_num

/-- **[Odd-denominator selection rule for Laughlin]** the Jain primary denominator `2p+1` is **odd** — the
incompressible fermionic Laughlin fractions. -/
lemma jainPrimary_denominator_odd (p : ℤ) : Odd (2 * p + 1) := ⟨p, by ring⟩

/-- **[Half-filling has even denominator]** the half-filled limit denominator `2p` is **even**, so `ν = 1/(2p)`
is *not* a fermionic Laughlin fraction (`jainPrimary_denominator_odd`). This is the precise reason the
even-denominator `ν=1/2` state requires a *paired* (Pfaffian) or compressible (CF Fermi sea) description — the
dichotomy the paper resolves. -/
lemma halfFilled_denominator_even (p : ℤ) : Even (2 * p) := ⟨p, by ring⟩

/-!

On the sphere the flux–particle relation reads `N_φ = N/ν − S`, where the **shift** `S` is a topological
quantum number. At a *fixed* filling, competing states have *different* shifts — so `S` distinguishes the
candidates the paper compares (the Moore–Read **Pfaffian** has `S = 3`, one unit above the would-be Laughlin
value), a sharper discriminator than the filling alone. -/

/-- The **flux–particle relation** `N_φ = N/ν − S` on the sphere (`S` = topological shift). -/
noncomputable def fluxFromShift (ν N S : ℝ) : ℝ := N / ν - S

/-- **[Laughlin shift `S = m`]** the `ν = 1/m` Laughlin state has `N_φ = mN − m`. -/
lemma laughlin_shift (m N : ℝ) : fluxFromShift (laughlinFilling m) N m = m * N - m := by
  unfold fluxFromShift laughlinFilling; rw [div_div_eq_mul_div, div_one]; ring

/-- **[Moore–Read Pfaffian shift `S = 3`]** the `ν = 1/2` Pfaffian has `N_φ = 2N − 3` — the one-component
paired state the paper identifies. -/
lemma pfaffian_flux (N : ℝ) : fluxFromShift (1 / 2) N 3 = 2 * N - 3 := by
  unfold fluxFromShift; rw [div_div_eq_mul_div, div_one]; ring

/-- **[The shift discriminates at fixed filling]** at the same `ν = 1/2`, the Pfaffian (`S = 3`) requires
**one more** flux quantum than the bosonic-Laughlin value (`S = 2`): `N_φ^{Pf} − N_φ^{L} = −1`. The shift is a
topological invariant that separates the candidate states the filling cannot. -/
lemma pfaffian_laughlin_shift_distinction (N : ℝ) :
    fluxFromShift (1 / 2) N 3 - fluxFromShift (1 / 2) N 2 = -1 := by
  unfold fluxFromShift; ring

/-- **[The `1/4 + 1/4` two-component CFFS]** the yellow-phase state of the paper: two composite-fermion seas,
each a `p = 2` half-filling analogue at `ν = 1/4` (even denominator `2·2 = 4`), summing to `ν = 1/2`. -/
lemma twoComponent_quarter_plus_quarter :
    (1 / 4 + 1 / 4 : ℝ) = 1 / 2 ∧ Even (2 * (2 : ℤ)) :=
  ⟨by norm_num, ⟨2, by ring⟩⟩


/-- The **inter-subband component defect** `K² − 1` of the bipartite `S`/`AS` two-mode system — the same
Schmidt invariant that measures the muon mode's entanglement. -/
noncomputable def componentEntanglementDefect (K : ℝ) : ℝ := K ^ 2 - 1

/-- **[One-component ⟺ unentangled subbands]** `K² − 1 = 0 ⟺ K = 1` (for `K > 0`) — the one-component state
(the paper's `ν=1/2` answer) is precisely the absence of inter-subband entanglement. -/
lemma oneComponent_iff_unentangled (K : ℝ) (hK : 0 < K) :
    componentEntanglementDefect K = 0 ↔ K = 1 := by
  unfold componentEntanglementDefect
  constructor
  · intro h
    have h2 : (K - 1) * (K + 1) = 0 := by nlinarith [h]
    rcases mul_eq_zero.mp h2 with h3 | h3 <;> linarith
  · intro h; rw [h]; ring

/-- **[A genuinely two-component state has positive defect]** `K > 1 ⟹ K² − 1 > 0` — e.g. the `(3,3,1)` state
the paper finds *dis*favoured has inter-subband entanglement `K > 1`. -/
lemma twoComponent_pos_defect (K : ℝ) (hK : 1 < K) : 0 < componentEntanglementDefect K := by
  unfold componentEntanglementDefect; nlinarith

/-- **[`g = 2K²` for the subband bipartition]** the effective g-factor of the component defect is twice the
squared Schmidt number — the muon-mode law `gFactor (K²−1) = 2K²`, instantiated for the `S`/`AS`
subbands. -/
lemma effective_gFactor_of_defect (K : ℝ) :
    gFactor (componentEntanglementDefect K) = 2 * K ^ 2 := by
  unfold componentEntanglementDefect; rw [gFactor]; ring

/-- **[One-component ⟹ effective `g = 2`]** the unentangled (one-component) limit `K = 1` gives the Dirac-like
value `g = 2` — the subband analogue of the muon's `g = 2 ⟺ K = 1`. -/
lemma oneComponent_effective_g_two : gFactor (componentEntanglementDefect 1) = 2 := by
  rw [effective_gFactor_of_defect]; norm_num

/-- **[The subband defect is the muon's `csch²η` defect]** `K² − 1 = anomaly η` when the inter-subband
Schmidt number is `K = coth η` — the `S`/`AS` entanglement and the muon mode are described by the *same*
hyperbolic defect (`anomaly_eq_schmidt_sq_sub_one`). -/
lemma subband_defect_eq_anomaly (η : ℝ) (hη : 0 < η) :
    componentEntanglementDefect (schmidtNumber η) = anomaly η :=
  (anomaly_eq_schmidt_sq_sub_one η hη).symm

/-- **[Subband effective g from the rapidity]** `g = 2 K² = 2 coth²η` — combines the bridge with
`gFactor_eq_two_schmidt_sq`, expressing the two-componentness directly in the inter-subband rapidity `η`. -/
lemma subband_effective_g (η : ℝ) (hη : 0 < η) :
    gFactor (componentEntanglementDefect (schmidtNumber η)) = 2 * (schmidtNumber η) ^ 2 := by
  rw [subband_defect_eq_anomaly η hη, gFactor_eq_two_schmidt_sq η hη]

/-!

A `ν = 1/m` Laughlin state is the low-energy `U(1)` Chern–Simons theory at **level `k = m`**. Its topological
ground-state degeneracy on the torus is `k = m` — exactly the dimension of the repository's level-`k`
Chern–Simons–Witten torus Hilbert space `TorusHilbert k`
(`ChernSimons.Gravity.torusHilbert_finrank`, "one state per integrable representation"). This
identifies the FQHE *inverse filling* with the CSW *level*, and the FQHE *topological ground-state degeneracy*
with the CSW Hilbert-space *dimension* — the same datum read in the quantum-Hall and the TQFT languages. -/

/-- The **`U(1)` Chern–Simons level** `k = m` of the `ν = 1/m` Laughlin state (= the inverse filling). -/
def laughlinChernSimonsLevel (m : ℕ) : ℕ := m

/-- **[FQHE filling ↔ CSW level ↔ torus degeneracy]** for the `ν = 1/m` Laughlin state, the inverse filling
equals the Chern–Simons level `m`, **and** the level-`m` CSW torus Hilbert space `TorusHilbert m` has dimension
`m` — the topological ground-state degeneracy. The FQHE filling fraction and the Chern–Simons TQFT torus
Hilbert space encode the same integer. -/
lemma laughlin_filling_eq_csw_torus_dim (m : ℕ) :
    (laughlinFilling (m : ℝ))⁻¹ = (m : ℝ) ∧
      Module.finrank ℂ (TorusHilbert (laughlinChernSimonsLevel m)) = m := by
  refine ⟨?_, ?_⟩
  · rw [laughlinFilling, one_div, inv_inv]
  · unfold laughlinChernSimonsLevel; exact torusHilbert_finrank m

/-- **[The `ν = 1/2` abelian sector has 2-fold torus degeneracy]** the `U(1)₂` charge sector of the half-filled
state: the level-2 CSW torus Hilbert space `TorusHilbert 2` is 2-dimensional. (The full Moore–Read Pfaffian
multiplies this `U(1)` sector by a non-abelian Ising factor — the source of its extra, non-abelian degeneracy,
beyond this abelian count.) -/
lemma halfFilling_abelian_torus_degeneracy :
    Module.finrank ℂ (TorusHilbert 2) = 2 :=
  torusHilbert_finrank 2

/-!

The Kitaev–Preskill topological entanglement entropy `γ = log D` (`D` = total quantum dimension) is the *same*
logarithm-of-an-entanglement-invariant as the muon mode entropy `S₂ = log K`
(`MuonAnomaly.EntanglementEntropy.renyi2Entropy`). For the abelian `U(1)_k` (`ν = 1/k`) order, `D = √k`, so
`γ = ½ log k`. Evaluated at the level-`k` CSW torus dimension (`§C`), this fuses the three repository faces of
the FQHE state into one integer `k`: the **Chern–Simons** torus degeneracy, the **entanglement-entropy**
machinery, and the **filling**. -/

/-- The **total quantum dimension** `D = √k` of the abelian `U(1)_k` (`ν = 1/k`) topological order — `k` anyons
of unit quantum dimension, `D = √(Σ_a d_a²) = √k`. -/
noncomputable def totalQuantumDimension (k : ℝ) : ℝ := Real.sqrt k

/-- The **topological entanglement entropy** `γ = log D` (Kitaev–Preskill), reusing the repository's
`renyi2Entropy = log` from the muon mode entanglement entropy. -/
noncomputable def topologicalEntanglementEntropy (k : ℝ) : ℝ :=
  renyi2Entropy (totalQuantumDimension k)

/-- **[`γ = ½ log k`]** the topological entanglement entropy of `U(1)_k` is half the log of the level. -/
lemma tee_eq_half_log_level (k : ℝ) (hk : 0 ≤ k) :
    topologicalEntanglementEntropy k = Real.log k / 2 := by
  unfold topologicalEntanglementEntropy totalQuantumDimension renyi2Entropy
  exact Real.log_sqrt hk

/-- **[The FQHE TEE from the Laughlin filling]** `γ = ½ log(1/ν) = ½ log m` for the `ν = 1/m` state. -/
lemma laughlin_tee (m : ℝ) (hm : 0 ≤ m) :
    topologicalEntanglementEntropy m = Real.log ((laughlinFilling m)⁻¹) / 2 := by
  rw [tee_eq_half_log_level m hm, laughlinFilling, one_div, inv_inv]

/-- **[The FQHE TEE from the CSW torus dimension — the three faces fused]** evaluated at the level-`m` CSW torus
Hilbert dimension (`§C`, `torusHilbert_finrank`), the topological entanglement entropy is `½ log m`. The
**Chern–Simons** degeneracy, the muon-mode **entropy** machinery (`renyi2Entropy`), and the FQHE
**filling** all reduce to the same integer `m`. -/
lemma tee_from_csw_torus_dimension (m : ℕ) :
    topologicalEntanglementEntropy (Module.finrank ℂ (TorusHilbert m) : ℝ) = Real.log m / 2 := by
  rw [torusHilbert_finrank]
  exact tee_eq_half_log_level (m : ℝ) (Nat.cast_nonneg m)

/-!

The repository instantiates the topological spin `ribbonTwist h = e^{2πi h}` only at bosons (integer `h`, `+1`)
and fermions (half-integer `h`, `−1`). The `ν = 1/m` Laughlin quasihole is the missing **anyon**: it carries the
fractional topological spin `h = 1/(2m)`, exchange phase `e^{iπ/m}`, whose **monodromy** (double exchange) is the
`U(1)_m` Wilson-line braiding phase `e^{2πi/m}` (`ChernSimons.WilsonLoopBraidingRibbon.wilsonBraidingPhase`). For
`m = 1` it is the electron (fermion, `−1`); for `m = 2` it is the **semion** — a square root of `−1`, provably
neither boson nor fermion: the first particle in the repository with statistics strictly between bosonic and
fermionic. -/

/-- **[Ribbon twist squares to twice the spin]** `(ribbonTwist h)² = ribbonTwist (2h)` — `e^{2πi h}` squared is
`e^{2πi(2h)}` (the exchange→monodromy doubling). -/
lemma ribbonTwist_sq (h : ℝ) : (ribbonTwist h) ^ 2 = ribbonTwist (2 * h) := by
  unfold ribbonTwist
  rw [pow_two, ← Complex.exp_add]
  congr 1
  push_cast; ring

/-- The **Laughlin anyon exchange phase** `e^{iπ/m} = ribbonTwist(1/(2m))` — the topological spin /
self-statistics of the `ν = 1/m` quasihole. -/
noncomputable def laughlinAnyonPhase (m : ℝ) : ℂ := ribbonTwist (1 / (2 * m))

/-- **[Spin–statistics: monodromy = exchange²]** `(e^{iπ/m})² = e^{2πi/m}` — the double-exchange (monodromy) of
two `ν = 1/m` Laughlin quasiholes is `ribbonTwist(1/m)`, the full braiding phase. -/
lemma laughlinAnyon_monodromy (m : ℝ) (hm : m ≠ 0) :
    (laughlinAnyonPhase m) ^ 2 = ribbonTwist (1 / m) := by
  unfold laughlinAnyonPhase
  rw [ribbonTwist_sq, show (2 : ℝ) * (1 / (2 * m)) = 1 / m from by field_simp]

/-- **[`m = 1` is the electron]** `laughlinAnyonPhase 1 = −1` — the integer-quantum-Hall limit recovers the
fermion. -/
lemma laughlinAnyon_fermion_at_one : laughlinAnyonPhase 1 = -1 := by
  unfold laughlinAnyonPhase
  rw [show (1 : ℝ) / (2 * 1) = 1 / 2 by norm_num]
  exact ribbonTwist_fermion

/-- **[The semion squares to `−1`]** `(laughlinAnyonPhase 2)² = −1` — the `ν = 1/2` quasihole monodromy is the
fermionic `−1`, so the exchange phase is a square root of `−1`. -/
lemma laughlinAnyon_semion_sq : (laughlinAnyonPhase 2) ^ 2 = -1 := by
  rw [laughlinAnyon_monodromy 2 (by norm_num)]; exact ribbonTwist_fermion

/-- **[The semion is genuinely anyonic]** `laughlinAnyonPhase 2 ∉ {1, −1}` — neither boson nor fermion, since
its square is `−1` while `(±1)² = 1`. This is the first particle in the repository with statistics strictly
between bosonic and fermionic — the anyon the boson/fermion dichotomy omits. -/
lemma laughlinAnyon_semion_not_boson_fermion :
    laughlinAnyonPhase 2 ≠ 1 ∧ laughlinAnyonPhase 2 ≠ -1 := by
  have hsq := laughlinAnyon_semion_sq
  refine ⟨fun h => ?_, fun h => ?_⟩ <;> rw [h] at hsq <;> norm_num at hsq

/-- **[The monodromy is the `U(1)_m` Wilson braiding phase]** `ribbonTwist(1/m) = wilsonBraidingPhase m a b` for
charge-1 anyons (`a.val = b.val = 1`) — the Laughlin quasihole monodromy **is** the Chern–Simons Wilson-line
braiding `e^{2πi/m}` of the `U(1)_m` theory (`§C`). This identifies the anyon's fractional statistics with the
repository's CSW braiding phase. -/
lemma laughlinAnyon_monodromy_eq_wilson (k : ℕ) (a b : Fin k)
    (ha : a.val = 1) (hb : b.val = 1) :
    ribbonTwist (1 / (k : ℝ)) = wilsonBraidingPhase k a b := by
  unfold ribbonTwist wilsonBraidingPhase
  rw [ha, hb]
  congr 1
  push_cast; ring

/-- **[Nontrivial monodromy for `m ≥ 2`]** `ribbonTwist(1/m) ≠ 1` — the `U(1)_m` braiding phase `e^{2πi/m}` is
not the identity (`1/m ∉ ℤ`), so two `ν = 1/m` quasiholes have genuinely nontrivial mutual statistics. -/
lemma ribbonTwist_one_div_ne_one (m : ℕ) (hm : 2 ≤ m) :
    ribbonTwist (1 / (m : ℝ)) ≠ 1 := by
  have hmpos : (0 : ℝ) < (m : ℝ) := by
    have h0 : 0 < m := by omega
    exact_mod_cast h0
  intro hcontra
  rw [ribbonTwist, Complex.exp_eq_one_iff] at hcontra
  obtain ⟨n, hn⟩ := hcontra
  have hcancel : (↑(2 * Real.pi * (1 / (m : ℝ))) : ℂ) = ↑n * (2 * (↑Real.pi : ℂ)) := by
    have h := hn
    rw [show (↑n : ℂ) * (2 * (↑Real.pi : ℂ) * Complex.I)
        = (↑n * (2 * (↑Real.pi : ℂ))) * Complex.I from by ring] at h
    exact mul_right_cancel₀ Complex.I_ne_zero h
  have hreal : 2 * Real.pi * (1 / (m : ℝ)) = (n : ℝ) * (2 * Real.pi) := by
    have hc : (↑(2 * Real.pi * (1 / (m : ℝ))) : ℂ) = ↑((n : ℝ) * (2 * Real.pi)) := by
      rw [hcancel]; push_cast; ring
    exact_mod_cast hc
  have h2pi : (2 * Real.pi) ≠ 0 := by positivity
  have hnm : (1 / (m : ℝ)) = (n : ℝ) := by
    have heq : (2 * Real.pi) * (1 / (m : ℝ)) = (2 * Real.pi) * (n : ℝ) := by rw [hreal]; ring
    exact mul_left_cancel₀ h2pi heq
  have hmR : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlo : (0 : ℝ) < (n : ℝ) := by rw [← hnm]; exact div_pos one_pos hmpos
  have hhi : (n : ℝ) < 1 := by rw [← hnm, div_lt_one hmpos]; linarith
  have hn0 : 0 < n := by exact_mod_cast hlo
  have hn1 : n < 1 := by exact_mod_cast hhi
  omega

/-- **[Every `ν = 1/m` (`m ≥ 2`) Laughlin quasihole is genuinely anyonic]** `laughlinAnyonPhase m ∉ {1, −1}` —
neither boson nor fermion, since its square is the nontrivial monodromy `ribbonTwist(1/m) ≠ 1` while `(±1)² = 1`.
This lifts the semion (`m = 2`) to the **entire** Laughlin sequence: every odd-denominator FQHE state carries an
anyonic quasihole. -/
lemma laughlinAnyon_genuinely_anyonic (m : ℕ) (hm : 2 ≤ m) :
    laughlinAnyonPhase (m : ℝ) ≠ 1 ∧ laughlinAnyonPhase (m : ℝ) ≠ -1 := by
  have hmne : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hmono : (laughlinAnyonPhase (m : ℝ)) ^ 2 = ribbonTwist (1 / (m : ℝ)) :=
    laughlinAnyon_monodromy (m : ℝ) hmne
  have hne := ribbonTwist_one_div_ne_one m hm
  exact ⟨fun h => hne (by rw [← hmono, h]; ring), fun h => hne (by rw [← hmono, h]; ring)⟩

/-!

The Laughlin quasihole has fractional charge `e/m` and statistical angle `θ = π/m`; eliminating `m` gives
the **charge–statistics relation** `θ = π q` — the hallmark of FQHE fractionalization, tying the anyon's
braiding phase to its fractional charge. -/

/-- The **Laughlin quasihole fractional charge** `q = 1/m` (in units of `e`): the `ν = 1/m` quasihole has
charge `e/m`. -/
noncomputable def laughlinQuasiholeCharge (m : ℝ) : ℝ := 1 / m

/-- The **statistical angle** `θ = π/m` of the `ν = 1/m` quasihole (exchange phase `e^{iθ}`). -/
noncomputable def laughlinStatisticalAngle (m : ℝ) : ℝ := Real.pi / m

/-- **[`m` quasiholes total unit charge]** `q · m = 1` — `m` fractional `e/m` quasiholes assemble one electron
charge (the quasihole is `1/m` of a charge). -/
lemma quasiholeCharge_mul_m (m : ℝ) (hm : m ≠ 0) : laughlinQuasiholeCharge m * m = 1 := by
  unfold laughlinQuasiholeCharge; field_simp

/-- **[The charge–statistics relation] `θ = π q`** — the statistical angle of the Laughlin quasihole is `π`
times its fractional charge. Fractional charge and fractional statistics are the same datum. -/
lemma charge_statistics_relation (m : ℝ) :
    laughlinStatisticalAngle m = Real.pi * laughlinQuasiholeCharge m := by
  unfold laughlinStatisticalAngle laughlinQuasiholeCharge; ring

/-- **[The exchange phase is `e^{iθ}`]** `laughlinAnyonPhase m = exp(iθ)` with `θ = π/m` — the anyon's exchange
phase is the exponential of its statistical angle (hence, by `charge_statistics_relation`, of `π` times its
charge). -/
lemma laughlinAnyonPhase_eq_exp_angle (m : ℝ) (hm : m ≠ 0) :
    laughlinAnyonPhase m = Complex.exp ((laughlinStatisticalAngle m : ℝ) * Complex.I) := by
  unfold laughlinAnyonPhase ribbonTwist laughlinStatisticalAngle
  rw [show (2 * Real.pi * (1 / (2 * m)) : ℝ) = Real.pi / m from by field_simp]

/-!

The paper argues the observed `ν = 1/2` state is the one-component **Moore–Read Pfaffian**, whose quasihole is a
**non-abelian Ising anyon** `σ` — unlike the abelian Laughlin quasiholes of §E. Its hallmarks are the quantum
dimension `d_σ = √2 > 1` (abelian anyons have `d = 1`), the multi-channel fusion `σ × σ = 1 + ψ`, and the
fractionalized `e/4` charge. -/

/-- The **Ising `σ` quantum dimension** `d_σ = √2` — the Moore–Read Pfaffian quasihole. -/
noncomputable def isingSigmaQuantumDimension : ℝ := Real.sqrt 2

/-- **[`d_σ² = 2`: the two fusion channels of `σ × σ = 1 + ψ`]** the `σ` quantum dimension squared counts the
fusion outcomes `1` and `ψ` (each of unit dimension): `d_σ² = d_1 + d_ψ = 1 + 1`. More than one fusion channel
is the defining feature of a non-abelian anyon. -/
lemma isingSigma_fusion_channels : isingSigmaQuantumDimension ^ 2 = 1 + 1 := by
  unfold isingSigmaQuantumDimension
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]; norm_num

/-- **[The Pfaffian quasihole is non-abelian]** `1 < d_σ` — `d_σ = √2 > 1`, so `σ` is a **non-abelian** anyon
(abelian anyons, including every Laughlin quasihole of §E, have `d = 1`). This is the qualitative distinction of
the paper's one-component Pfaffian. -/
lemma isingSigma_nonabelian : 1 < isingSigmaQuantumDimension := by
  unfold isingSigmaQuantumDimension
  rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- **[Ising total quantum dimension `D = 2`]** `D = √(d_1² + d_σ² + d_ψ²) = √(1 + 2 + 1) = 2` — the anyon
content `{1, σ, ψ}` of the Moore–Read state. -/
lemma ising_total_quantum_dimension :
    Real.sqrt (1 + isingSigmaQuantumDimension ^ 2 + 1) = 2 := by
  rw [isingSigma_fusion_channels,
    show (1 : ℝ) + (1 + 1) + 1 = 2 ^ 2 from by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]

/-- **[The `σ` topological spin is nontrivial]** `ribbonTwist(1/16) ≠ 1` — the Ising `σ` has conformal spin
`h_σ = 1/16` (exchange phase `e^{iπ/8}`), genuinely anyonic self-statistics (reuses
`ribbonTwist_one_div_ne_one`). -/
lemma isingSigma_twist_ne_one : ribbonTwist (1 / (16 : ℝ)) ≠ 1 :=
  ribbonTwist_one_div_ne_one 16 (by norm_num)

/-- The **Moore–Read quasihole charge** `e/4` (in units of `e`) — the Pfaffian fractionalizes charge *further*
than the abelian `ν = 1/2`. -/
noncomputable def pfaffianQuasiholeCharge : ℝ := 1 / 4

/-- **[The Pfaffian quasihole is more fractionalized than the abelian `ν=1/2`]** `e/4 < e/2`: the Moore–Read
fundamental charge `1/4` is half the abelian `ν = 1/2` value `laughlinQuasiholeCharge 2 = 1/2`. -/
lemma pfaffian_charge_lt_laughlin :
    pfaffianQuasiholeCharge < laughlinQuasiholeCharge 2 := by
  unfold pfaffianQuasiholeCharge laughlinQuasiholeCharge; norm_num


/-- The half-filled FQHE semion and the `U(1)₂` CSW Wilson-loop semion are the
same repository capability: the Hall side proves the exchange phase is neither
bosonic nor fermionic, while the CSW side supplies the Wilson conformal weight,
ribbon topological spin, and Verlinde braiding row. -/
def HasHalfFillingSemionChernSimonsBridge : Prop :=
  HasSemionAnyonCarrier
    ∧ (laughlinAnyonPhase 2) ^ 2 = -1
    ∧ laughlinAnyonPhase 2 ≠ 1
    ∧ laughlinAnyonPhase 2 ≠ -1
    ∧ wilsonTopologicalSpin 2 semionCharge = ribbonTwist (1 / 4)
    ∧ (∀ b : Fin 2,
      wilsonBraidingPhase 2 semionCharge b =
        (Real.sqrt 2 : ℂ) * (starRingEnd ℂ) (cswSMatrix 2 semionCharge b))

/-- The half-filled FQHE anyon and the CSW `U(1)₂` Wilson-line semion are linked
without restating either construction. -/
lemma halfFilling_semion_csw_bridge_checked :
    HasHalfFillingSemionChernSimonsBridge := by
  rcases laughlinAnyon_semion_not_boson_fermion with ⟨hnotBoson, hnotFermion⟩
  exact ⟨semionAnyonCarrier_checked, laughlinAnyon_semion_sq, hnotBoson, hnotFermion,
    semionTopologicalSpin_eq_quarterRibbon, semionBraidingPhase_eq_S⟩

/-- The `ν = 1/2` abelian sector is the checked `U(1)₂` abelian anyon sector. -/
lemma halfFilling_abelian_anyon_sector :
    HasAbelianAnyonSector 2 (by norm_num) :=
  abelianAnyonSector_checked 2 (by norm_num)


/-- The Hall conductance in units of `e²/h`: `σ_H/(e²/h) = ν`. -/
noncomputable def hallConductanceUnits (ν : ℝ) : ℝ := ν

/-- The Hall resistivity in units of `h/e²`: `ρ_xy/(h/e²) = 1/ν`. -/
noncomputable def hallResistivityUnits (ν : ℝ) : ℝ := ν⁻¹

/-- The Laughlin `ν = 1/m` state has Hall conductance `1/m` in units of `e²/h`. -/
lemma laughlin_hallConductance (m : ℝ) :
    hallConductanceUnits (laughlinFilling m) = 1 / m := rfl

/-- The Laughlin `ν = 1/m` state has Hall resistivity `m` in units of `h/e²`. -/
lemma laughlin_hallResistivity (m : ℝ) :
    hallResistivityUnits (laughlinFilling m) = m := by
  unfold hallResistivityUnits laughlinFilling
  rw [one_div, inv_inv]

/-- The Jain state `ν = n/(2pn+1)` has Hall conductance equal to that filling. -/
lemma jain_hallConductance (n p : ℝ) :
    hallConductanceUnits (jainFilling n p) = n / (2 * p * n + 1) := rfl

/-- The half-filled state has Hall conductance `1/2` in units of `e²/h`. -/
lemma halfFilling_hallConductance :
    hallConductanceUnits (1 / 2) = 1 / 2 := rfl

/-- The half-filled state has Hall resistivity `2` in units of `h/e²`. -/
lemma halfFilling_hallResistivity :
    hallResistivityUnits (1 / 2) = 2 := by
  unfold hallResistivityUnits
  norm_num


/-- Filling fraction of the symmetric two-component Halperin `(m,m,n)` state:
`ν = tᵀK⁻¹t = 2/(m+n)` for `K = [[m,n],[n,m]]` and charge vector `t=(1,1)`. -/
noncomputable def halperinFilling (m n : ℝ) : ℝ := 2 / (m + n)

/-- Torus ground-state degeneracy of the symmetric Halperin state:
`|det K| = m² - n²` in the positive `m > n` case. -/
def halperinTorusDegeneracy (m n : ℤ) : ℤ := m * m - n * n

/-- Fundamental quasihole charge of the symmetric Halperin `(m,m,n)` state:
`q = 1/(m+n)` in units of `e`. -/
noncomputable def halperinQuasiholeCharge (m n : ℝ) : ℝ := 1 / (m + n)

/-- Self-statistics angle of the layer quasihole in the symmetric Halperin state:
`θ_self = π m/(m²-n²)`. -/
noncomputable def halperinSelfStatisticsAngle (m n : ℝ) : ℝ :=
  Real.pi * m / (m ^ 2 - n ^ 2)

/-- Mutual-statistics angle of the two layer quasiholes in the symmetric Halperin state:
`θ_mutual = -π n/(m²-n²)`. -/
noncomputable def halperinMutualStatisticsAngle (m n : ℝ) : ℝ :=
  -Real.pi * n / (m ^ 2 - n ^ 2)


/-- The symmetric two-component Halperin K-matrix `K = [[m,n],[n,m]]`. -/
noncomputable def halperinKMatrix (m n : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![m, n; n, m]

/-- The explicit inverse of the symmetric Halperin K-matrix:
`K⁻¹ = 1/(m²-n²) [[m,-n],[-n,m]]`. -/
noncomputable def halperinKInverse (m n : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  (1 / (m ^ 2 - n ^ 2)) • !![m, -n; -n, m]

/-- The charge vector `t = (1,1)` for the two-component Halperin state. -/
def halperinChargeVector : Fin 2 → ℝ := fun _ => 1

/-- The K-matrix filling formula `ν = tᵀK⁻¹t`. -/
noncomputable def halperinFillingFromK (m n : ℝ) : ℝ :=
  ∑ i : Fin 2, ∑ j : Fin 2,
    halperinChargeVector i * halperinKInverse m n i j * halperinChargeVector j

/-- The layer-one fundamental quasihole charge from K-matrix data:
`q = tᵀK⁻¹e₁`. -/
noncomputable def halperinLayerQuasiholeChargeFromK (m n : ℝ) : ℝ :=
  ∑ i : Fin 2, halperinChargeVector i * halperinKInverse m n i 0

/-- The layer-one self-statistics angle from the K-matrix inverse:
`θ = π (K⁻¹)₁₁`. -/
noncomputable def halperinSelfStatisticsAngleFromK (m n : ℝ) : ℝ :=
  Real.pi * halperinKInverse m n 0 0

/-- The mutual-statistics angle from the K-matrix inverse:
`θ = π (K⁻¹)₁₂`. -/
noncomputable def halperinMutualStatisticsAngleFromK (m n : ℝ) : ℝ :=
  Real.pi * halperinKInverse m n 0 1

/-- The displayed `K⁻¹` is a left inverse whenever `m²-n² ≠ 0`. -/
lemma halperinKInverse_mul_KMatrix (m n : ℝ) (hdet : m ^ 2 - n ^ 2 ≠ 0) :
    halperinKInverse m n * halperinKMatrix m n = 1 := by
  ext i j
  fin_cases i
  · fin_cases j
    · simp [halperinKInverse, halperinKMatrix, Matrix.mul_apply, Fin.sum_univ_two]
      field_simp [hdet]
      ring
    · simp [halperinKInverse, halperinKMatrix, Matrix.mul_apply, Fin.sum_univ_two]
      field_simp [hdet]
      ring
  · fin_cases j
    · simp [halperinKInverse, halperinKMatrix, Matrix.mul_apply, Fin.sum_univ_two]
      field_simp [hdet]
      ring
    · simp [halperinKInverse, halperinKMatrix, Matrix.mul_apply, Fin.sum_univ_two]
      field_simp [hdet]
      ring

/-- The displayed `K⁻¹` is a right inverse whenever `m²-n² ≠ 0`. -/
lemma halperinKMatrix_mul_KInverse (m n : ℝ) (hdet : m ^ 2 - n ^ 2 ≠ 0) :
    halperinKMatrix m n * halperinKInverse m n = 1 := by
  ext i j
  fin_cases i
  · fin_cases j
    · simp [halperinKInverse, halperinKMatrix, Matrix.mul_apply, Fin.sum_univ_two]
      field_simp [hdet]
      ring
    · simp [halperinKInverse, halperinKMatrix, Matrix.mul_apply, Fin.sum_univ_two]
      field_simp [hdet]
      ring
  · fin_cases j
    · simp [halperinKInverse, halperinKMatrix, Matrix.mul_apply, Fin.sum_univ_two]
      field_simp [hdet]
      ring
    · simp [halperinKInverse, halperinKMatrix, Matrix.mul_apply, Fin.sum_univ_two]
      field_simp [hdet]
      ring

/-- The K-matrix formula `tᵀK⁻¹t` derives the symmetric Halperin filling
`2/(m+n)`. -/
lemma halperinFillingFromK_eq (m n : ℝ)
    (hdet : m ^ 2 - n ^ 2 ≠ 0) (hsum : m + n ≠ 0) :
    halperinFillingFromK m n = halperinFilling m n := by
  unfold halperinFillingFromK halperinFilling halperinChargeVector halperinKInverse
  simp [Fin.sum_univ_two]
  field_simp [hdet, hsum]
  ring

/-- The K-matrix formula `tᵀK⁻¹e₁` derives the fundamental quasihole charge
`1/(m+n)`. -/
lemma halperinLayerQuasiholeChargeFromK_eq (m n : ℝ)
    (hdet : m ^ 2 - n ^ 2 ≠ 0) (hsum : m + n ≠ 0) :
    halperinLayerQuasiholeChargeFromK m n = halperinQuasiholeCharge m n := by
  unfold halperinLayerQuasiholeChargeFromK halperinQuasiholeCharge halperinChargeVector
    halperinKInverse
  simp [Fin.sum_univ_two]
  field_simp [hdet, hsum]
  ring

/-- The K-matrix inverse derives the self-statistics angle. -/
lemma halperinSelfStatisticsAngleFromK_eq (m n : ℝ) :
    halperinSelfStatisticsAngleFromK m n = halperinSelfStatisticsAngle m n := by
  simp [halperinSelfStatisticsAngleFromK, halperinSelfStatisticsAngle, halperinKInverse]
  ring

/-- The K-matrix inverse derives the mutual-statistics angle. -/
lemma halperinMutualStatisticsAngleFromK_eq (m n : ℝ) :
    halperinMutualStatisticsAngleFromK m n = halperinMutualStatisticsAngle m n := by
  simp [halperinMutualStatisticsAngleFromK, halperinMutualStatisticsAngle, halperinKInverse]
  ring

/-- The two-component Halperin `(3,3,1)` candidate is also at half filling. -/
lemma halperin331_filling :
    halperinFilling 3 1 = 1 / 2 := by
  norm_num [halperinFilling]

/-- The `(3,3,1)` K-matrix has torus degeneracy `8`. -/
lemma halperin331_torus_degeneracy :
    halperinTorusDegeneracy 3 1 = 8 := by
  norm_num [halperinTorusDegeneracy]

/-- The fundamental `(3,3,1)` quasihole has charge `e/4`. -/
lemma halperin331_quasihole_charge :
    halperinQuasiholeCharge 3 1 = 1 / 4 := by
  norm_num [halperinQuasiholeCharge]

/-- Two `(3,3,1)` fundamental quasiholes carry the same total charge as the
abelian `ν = 1/2` Laughlin quasihole. -/
lemma two_halperin331_quasiholes_eq_laughlin_half_charge :
    2 * halperinQuasiholeCharge 3 1 = laughlinQuasiholeCharge 2 := by
  norm_num [halperinQuasiholeCharge, laughlinQuasiholeCharge]

/-- The `(3,3,1)` self-statistics angle is `3π/8`. -/
lemma halperin331_selfStatisticsAngle :
    halperinSelfStatisticsAngle 3 1 = 3 * Real.pi / 8 := by
  unfold halperinSelfStatisticsAngle
  ring_nf

/-- The `(3,3,1)` mutual-statistics angle is `-π/8`. -/
lemma halperin331_mutualStatisticsAngle :
    halperinMutualStatisticsAngle 3 1 = -Real.pi / 8 := by
  unfold halperinMutualStatisticsAngle
  ring_nf

/-- The complete `(3,3,1)` formulas are derived from the explicit K-matrix
inverse, then evaluated to the standard half-filling values. -/
def HasHalperin331KMatrixDerivation : Prop :=
  halperinKInverse 3 1 * halperinKMatrix 3 1 = 1
    ∧ halperinKMatrix 3 1 * halperinKInverse 3 1 = 1
    ∧ halperinFillingFromK 3 1 = halperinFilling 3 1
    ∧ halperinLayerQuasiholeChargeFromK 3 1 = halperinQuasiholeCharge 3 1
    ∧ halperinSelfStatisticsAngleFromK 3 1 = halperinSelfStatisticsAngle 3 1
    ∧ halperinMutualStatisticsAngleFromK 3 1 = halperinMutualStatisticsAngle 3 1
    ∧ halperinFilling 3 1 = 1 / 2
    ∧ halperinQuasiholeCharge 3 1 = 1 / 4
    ∧ halperinTorusDegeneracy 3 1 = 8

/-- The `(3,3,1)` K-matrix derivation is checked in Lean. -/
lemma halperin331_kmatrix_derivation_checked :
    HasHalperin331KMatrixDerivation :=
  ⟨halperinKInverse_mul_KMatrix 3 1 (by norm_num),
    halperinKMatrix_mul_KInverse 3 1 (by norm_num),
    halperinFillingFromK_eq 3 1 (by norm_num) (by norm_num),
    halperinLayerQuasiholeChargeFromK_eq 3 1 (by norm_num) (by norm_num),
    halperinSelfStatisticsAngleFromK_eq 3 1,
    halperinMutualStatisticsAngleFromK_eq 3 1,
    halperin331_filling,
    halperin331_quasihole_charge,
    halperin331_torus_degeneracy⟩


/-- Chiral central charge of the Moore--Read Pfaffian edge:
one charged boson plus one Majorana mode, `c = 1 + 1/2 = 3/2`. -/
noncomputable def pfaffianChiralCentralCharge : ℝ := 3 / 2

/-- Chiral central charge of the abelian two-component `(3,3,1)` edge:
two charged bosonic edge modes, `c = 2`. -/
noncomputable def halperin331ChiralCentralCharge : ℝ := 2

/-- The Pfaffian and `(3,3,1)` candidates have different chiral central charge. -/
lemma pfaffian_chiralCentralCharge_ne_halperin331 :
    pfaffianChiralCentralCharge ≠ halperin331ChiralCentralCharge := by
  norm_num [pfaffianChiralCentralCharge, halperin331ChiralCentralCharge]

/-- The two principal `ν = 1/2` candidates have the same filling but different
topological signatures: Pfaffian has shift `3`, non-abelian Ising `σ`, and
central charge `3/2`; `(3,3,1)` has K-matrix degeneracy `8`, abelian charge
`e/4`, and central charge `2`. -/
def HasHalfFillingCandidateDiscriminators : Prop :=
  halperinFilling 3 1 = 1 / 2
    ∧ fluxFromShift (1 / 2) 1 3 = -1
    ∧ isingSigmaQuantumDimension ^ 2 = 1 + 1
    ∧ 1 < isingSigmaQuantumDimension
    ∧ halperinTorusDegeneracy 3 1 = 8
    ∧ halperinQuasiholeCharge 3 1 = 1 / 4
    ∧ HasHalperin331KMatrixDerivation
    ∧ pfaffianQuasiholeCharge < laughlinQuasiholeCharge 2
    ∧ pfaffianChiralCentralCharge ≠ halperin331ChiralCentralCharge

/-- The half-filling Pfaffian-vs-`(3,3,1)` discriminators are checked from the
existing FQHE arithmetic, Ising-anyon, and K-matrix-shadow facts. -/
lemma halfFilling_candidate_discriminators_checked :
    HasHalfFillingCandidateDiscriminators :=
  ⟨halperin331_filling,
    by norm_num [fluxFromShift],
    isingSigma_fusion_channels,
    isingSigma_nonabelian,
    halperin331_torus_degeneracy,
    halperin331_quasihole_charge,
    halperin331_kmatrix_derivation_checked,
    pfaffian_charge_lt_laughlin,
    pfaffian_chiralCentralCharge_ne_halperin331⟩


/-- The thermal Hall conductance in units of `π² k_B² T/(3h)` is the chiral
central charge `c_-`. -/
noncomputable def thermalHallConductanceUnits (cMinus : ℝ) : ℝ := cMinus

/-- The edge central charge assembled from charged and neutral edge sectors. -/
noncomputable def edgeModeCentralCharge (charged neutral : ℝ) : ℝ :=
  charged + neutral

/-- The Moore--Read Pfaffian edge has one charged boson and one Majorana mode. -/
lemma pfaffian_edgeModeCentralCharge :
    edgeModeCentralCharge 1 (1 / 2) = pfaffianChiralCentralCharge := by
  norm_num [edgeModeCentralCharge, pfaffianChiralCentralCharge]

/-- The `(3,3,1)` edge has two bosonic charged modes and no Majorana mode. -/
lemma halperin331_edgeModeCentralCharge :
    edgeModeCentralCharge 2 0 = halperin331ChiralCentralCharge := by
  norm_num [edgeModeCentralCharge, halperin331ChiralCentralCharge]

/-- The Pfaffian thermal Hall response is `3/2` in natural thermal-Hall units. -/
lemma pfaffian_thermalHallConductance :
    thermalHallConductanceUnits pfaffianChiralCentralCharge = 3 / 2 := by
  norm_num [thermalHallConductanceUnits, pfaffianChiralCentralCharge]

/-- The `(3,3,1)` thermal Hall response is `2` in natural thermal-Hall units. -/
lemma halperin331_thermalHallConductance :
    thermalHallConductanceUnits halperin331ChiralCentralCharge = 2 := by
  norm_num [thermalHallConductanceUnits, halperin331ChiralCentralCharge]

/-- Thermal Hall conductance separates the two half-filling candidates by `1/2`. -/
lemma thermalHall_pfaffian_halperin331_gap :
    thermalHallConductanceUnits halperin331ChiralCentralCharge -
      thermalHallConductanceUnits pfaffianChiralCentralCharge = 1 / 2 := by
  norm_num [thermalHallConductanceUnits, pfaffianChiralCentralCharge,
    halperin331ChiralCentralCharge]

/-- The half-filling bulk-edge response combines quantized electric Hall data,
edge central charges, and thermal-Hall discrimination. -/
def HasHalfFillingBulkEdgeResponse : Prop :=
  hallConductanceUnits (1 / 2) = 1 / 2
    ∧ hallResistivityUnits (1 / 2) = 2
    ∧ edgeModeCentralCharge 1 (1 / 2) = pfaffianChiralCentralCharge
    ∧ edgeModeCentralCharge 2 0 = halperin331ChiralCentralCharge
    ∧ thermalHallConductanceUnits pfaffianChiralCentralCharge = 3 / 2
    ∧ thermalHallConductanceUnits halperin331ChiralCentralCharge = 2
    ∧ thermalHallConductanceUnits halperin331ChiralCentralCharge -
      thermalHallConductanceUnits pfaffianChiralCentralCharge = 1 / 2

/-- The half-filling bulk-edge response is checked from the Hall-conductance
definitions and the candidate central charges. -/
lemma halfFilling_bulkEdgeResponse_checked :
    HasHalfFillingBulkEdgeResponse :=
  ⟨halfFilling_hallConductance,
    halfFilling_hallResistivity,
    pfaffian_edgeModeCentralCharge,
    halperin331_edgeModeCentralCharge,
    pfaffian_thermalHallConductance,
    halperin331_thermalHallConductance,
    thermalHall_pfaffian_halperin331_gap⟩


/-- A uniform topological anyon model: normalized charge, conformal weight,
exchange phase, monodromy phase, quantum dimension, and fusion-channel count. -/
structure AnyonModel where
  chargeUnits : ℝ
  conformalWeight : ℝ
  exchangePhase : ℂ
  monodromyPhase : ℂ
  quantumDimension : ℝ
  fusionChannelCount : ℕ

/-- The named anyon families currently present in the FQHE/CSW sector. The
`laughlinQuasihole m` and `wilsonLine k a` constructors are parametric, so this
is not a finite hand table: it covers the whole Laughlin sequence and every
`U(1)_k` Wilson-line anyon. -/
inductive NamedAnyon : Type
  | laughlinQuasihole (m : ℕ)
  | wilsonLine (k : ℕ) (a : Fin k)
  | isingVacuum
  | isingSigma
  | isingPsi
  | halperin331Layer

/-- Parameterized model for every abelian `U(1)_k` Wilson-line anyon. This
retains the full braiding row against every other charge in the same level. -/
structure AbelianWilsonAnyonModel (k : ℕ) where
  charge : Fin k
  conformalWeight : ℝ
  topologicalSpin : ℂ
  quantumDimension : ℝ
  braidingPhase : Fin k → ℂ

/-- Generic constructor for an abelian Wilson-line anyon at level `k`. -/
noncomputable def abelianWilsonAnyonModel (k : ℕ) (a : Fin k) :
    AbelianWilsonAnyonModel k where
  charge := a
  conformalWeight := wilsonConformalWeight k a
  topologicalSpin := wilsonTopologicalSpin k a
  quantumDimension := 1
  braidingPhase := fun b => wilsonBraidingPhase k a b

/-- The generated Wilson-line model has the ribbon topological spin supplied by
the CSW Wilson-loop infrastructure. -/
lemma abelianWilsonAnyonModel_topologicalSpin_eq_ribbon
    (k : ℕ) (a : Fin k) :
    (abelianWilsonAnyonModel k a).topologicalSpin =
      ribbonTwist (abelianWilsonAnyonModel k a).conformalWeight := by
  simp [abelianWilsonAnyonModel, wilsonTopologicalSpin]

/-- The generated Wilson-line model has the Verlinde `S`-matrix braiding row. -/
lemma abelianWilsonAnyonModel_braiding_eq_S
    (k : ℕ) (hk : 0 < k) (a b : Fin k) :
    (abelianWilsonAnyonModel k a).braidingPhase b =
      (Real.sqrt k : ℂ) * (starRingEnd ℂ) (cswSMatrix k a b) := by
  simpa [abelianWilsonAnyonModel] using wilsonBraidingPhase_eq_S k hk a b

/-- The generated Wilson-line models are abelian: every line has unit quantum
dimension. -/
lemma abelianWilsonAnyonModel_quantumDimension
    (k : ℕ) (a : Fin k) :
    (abelianWilsonAnyonModel k a).quantumDimension = 1 := rfl

/-- Generic constructor for the named anyon taxonomy. The definitions call the
already-formalized FQHE/CSW formulas; no statistics, charge, or fusion equation
is redefined in a separate table. -/
noncomputable def namedAnyonModel : NamedAnyon → AnyonModel
  | NamedAnyon.laughlinQuasihole m =>
      { chargeUnits := laughlinQuasiholeCharge (m : ℝ)
        conformalWeight := 1 / (2 * (m : ℝ))
        exchangePhase := laughlinAnyonPhase (m : ℝ)
        monodromyPhase := (laughlinAnyonPhase (m : ℝ)) ^ 2
        quantumDimension := 1
        fusionChannelCount := 1 }
  | NamedAnyon.wilsonLine k a =>
      { chargeUnits := (a.val : ℝ) / (k : ℝ)
        conformalWeight := wilsonConformalWeight k a
        exchangePhase := wilsonTopologicalSpin k a
        monodromyPhase := (wilsonTopologicalSpin k a) ^ 2
        quantumDimension := 1
        fusionChannelCount := 1 }
  | NamedAnyon.isingVacuum =>
      { chargeUnits := 0
        conformalWeight := 0
        exchangePhase := ribbonTwist 0
        monodromyPhase := (ribbonTwist 0) ^ 2
        quantumDimension := 1
        fusionChannelCount := 1 }
  | NamedAnyon.isingSigma =>
      { chargeUnits := pfaffianQuasiholeCharge
        conformalWeight := 1 / 16
        exchangePhase := ribbonTwist (1 / 16)
        monodromyPhase := (ribbonTwist (1 / 16)) ^ 2
        quantumDimension := isingSigmaQuantumDimension
        fusionChannelCount := 2 }
  | NamedAnyon.isingPsi =>
      { chargeUnits := 0
        conformalWeight := 1 / 2
        exchangePhase := ribbonTwist (1 / 2)
        monodromyPhase := (ribbonTwist (1 / 2)) ^ 2
        quantumDimension := 1
        fusionChannelCount := 1 }
  | NamedAnyon.halperin331Layer =>
      { chargeUnits := halperinQuasiholeCharge 3 1
        conformalWeight := 3 / 16
        exchangePhase := ribbonTwist (3 / 16)
        monodromyPhase := (ribbonTwist (3 / 16)) ^ 2
        quantumDimension := 1
        fusionChannelCount := 1 }

/-- Every generated named-anyon model uses exchange phase equal to the ribbon
twist at its conformal weight. -/
lemma namedAnyonModel_exchange_eq_ribbonTwist (A : NamedAnyon) :
    (namedAnyonModel A).exchangePhase =
      ribbonTwist (namedAnyonModel A).conformalWeight := by
  cases A <;> rfl

/-- The generated monodromy field is the square of the generated exchange
phase, uniformly for all named anyons. -/
lemma namedAnyonModel_monodromy_eq_exchange_sq (A : NamedAnyon) :
    (namedAnyonModel A).monodromyPhase =
      (namedAnyonModel A).exchangePhase ^ 2 := by
  cases A <;> rfl

/-- Every generated named-anyon exchange phase lies on the unit circle, using
the repository's abstract exchange-statistics spectrum. -/
lemma namedAnyonModel_exchange_unit (A : NamedAnyon) :
    ‖(namedAnyonModel A).exchangePhase‖ = 1 := by
  rw [namedAnyonModel_exchange_eq_ribbonTwist]
  exact exchangePhase_unit (namedAnyonModel A).conformalWeight

/-- The generated monodromy agrees with the abstract exchange-statistics
monodromy operation. -/
lemma namedAnyonModel_monodromy_eq_exchangeSpectrum (A : NamedAnyon) :
    monodromy (namedAnyonModel A).exchangePhase =
      (namedAnyonModel A).monodromyPhase := by
  rw [monodromy, namedAnyonModel_monodromy_eq_exchange_sq]

/-- The Laughlin generated model recovers the existing monodromy formula
`exchange² = ribbonTwist(1/m)` whenever `m ≠ 0`. -/
lemma laughlinAnyonModel_monodromy_eq_ribbon (m : ℕ) (hm : m ≠ 0) :
    (namedAnyonModel (NamedAnyon.laughlinQuasihole m)).monodromyPhase =
      ribbonTwist (1 / (m : ℝ)) := by
  simpa [namedAnyonModel] using
    laughlinAnyon_monodromy (m : ℝ) (Nat.cast_ne_zero.mpr hm)

/-- The Laughlin generated model satisfies the charge-statistics relation. -/
lemma laughlinAnyonModel_charge_statistics (m : ℕ) :
    laughlinStatisticalAngle (m : ℝ) =
      Real.pi * (namedAnyonModel (NamedAnyon.laughlinQuasihole m)).chargeUnits := by
  simpa [namedAnyonModel] using charge_statistics_relation (m : ℝ)

/-- Every physical Laughlin quasihole model with `m ≥ 2` is genuinely anyonic:
its exchange phase is neither bosonic nor fermionic. -/
lemma laughlinAnyonModel_genuinely_anyonic (m : ℕ) (hm : 2 ≤ m) :
    (namedAnyonModel (NamedAnyon.laughlinQuasihole m)).exchangePhase ≠ 1
      ∧ (namedAnyonModel (NamedAnyon.laughlinQuasihole m)).exchangePhase ≠ -1 := by
  simpa [namedAnyonModel] using laughlinAnyon_genuinely_anyonic m hm

/-- Every physical Laughlin quasihole model with `m ≥ 2` satisfies the
repository's abstract `IsAnyonic` predicate. -/
lemma laughlinAnyonModel_isAnyonic (m : ℕ) (hm : 2 ≤ m) :
    IsAnyonic (namedAnyonModel (NamedAnyon.laughlinQuasihole m)).exchangePhase := by
  rcases laughlinAnyonModel_genuinely_anyonic m hm with ⟨hBoson, hFermion⟩
  exact ⟨namedAnyonModel_exchange_unit (NamedAnyon.laughlinQuasihole m),
    hBoson, hFermion⟩

/-- The named semion model is the `m = 2` Laughlin quasihole. -/
noncomputable def semionAnyonModel : AnyonModel :=
  namedAnyonModel (NamedAnyon.laughlinQuasihole 2)

/-- The generated semion model is neither bosonic nor fermionic. -/
lemma semionAnyonModel_not_boson_fermion :
    semionAnyonModel.exchangePhase ≠ 1 ∧ semionAnyonModel.exchangePhase ≠ -1 := by
  simpa [semionAnyonModel, namedAnyonModel] using laughlinAnyon_semion_not_boson_fermion

/-- The generated semion model has monodromy `−1`. -/
lemma semionAnyonModel_monodromy :
    semionAnyonModel.monodromyPhase = -1 := by
  simpa [semionAnyonModel, namedAnyonModel] using laughlinAnyon_semion_sq

/-- The generated semion model is an anyon in the abstract
exchange-statistics spectrum. -/
lemma semionAnyonModel_isAnyonic :
    IsAnyonic semionAnyonModel.exchangePhase := by
  rcases semionAnyonModel_not_boson_fermion with ⟨hBoson, hFermion⟩
  exact ⟨by
      simpa [semionAnyonModel] using
        namedAnyonModel_exchange_unit (NamedAnyon.laughlinQuasihole 2),
    hBoson, hFermion⟩

/-- The generated Ising `σ` model is non-abelian: its quantum dimension is
strictly larger than one. -/
lemma isingSigmaAnyonModel_nonabelian :
    1 < (namedAnyonModel NamedAnyon.isingSigma).quantumDimension := by
  simpa [namedAnyonModel] using isingSigma_nonabelian

/-- The generated Ising `σ` model has the two-channel fusion count
corresponding to `σ × σ = 1 + ψ`. -/
lemma isingSigmaAnyonModel_fusionChannelCount :
    (namedAnyonModel NamedAnyon.isingSigma).fusionChannelCount = 2 := rfl

/-- The generated Ising `ψ` model has fermion exchange phase. -/
lemma isingPsiAnyonModel_fermion_phase :
    (namedAnyonModel NamedAnyon.isingPsi).exchangePhase = -1 := by
  simpa [namedAnyonModel] using ribbonTwist_fermion

/-- The generated Ising vacuum model has boson exchange phase. -/
lemma isingVacuumAnyonModel_boson_phase :
    (namedAnyonModel NamedAnyon.isingVacuum).exchangePhase = 1 := by
  simpa [namedAnyonModel] using ribbonTwist_boson 0

/-- The generated Halperin `(3,3,1)` layer quasihole model has charge `e/4`. -/
lemma halperin331LayerAnyonModel_charge :
    (namedAnyonModel NamedAnyon.halperin331Layer).chargeUnits = 1 / 4 := by
  simpa [namedAnyonModel] using halperin331_quasihole_charge

/-- The generated Halperin `(3,3,1)` layer quasihole has conformal weight
`3/16`, equivalent to self-statistics angle `3π/8`. -/
lemma halperin331LayerAnyonModel_selfStatistics :
    2 * Real.pi * (namedAnyonModel NamedAnyon.halperin331Layer).conformalWeight =
      halperinSelfStatisticsAngle 3 1 := by
  rw [halperin331_selfStatisticsAngle]
  norm_num [namedAnyonModel]
  ring

/-- Capability predicate for the generated anyon models. It includes the whole
Laughlin sequence, every abelian Wilson-line anyon, the half-filled semion, the
Moore--Read Ising sector, and the Halperin `(3,3,1)` K-matrix anyon. -/
def HasDataDrivenAnyonModels : Prop :=
  (∀ A : NamedAnyon,
      (namedAnyonModel A).exchangePhase =
        ribbonTwist (namedAnyonModel A).conformalWeight)
    ∧ (∀ A : NamedAnyon,
      (namedAnyonModel A).monodromyPhase =
        (namedAnyonModel A).exchangePhase ^ 2)
    ∧ (∀ A : NamedAnyon,
      ‖(namedAnyonModel A).exchangePhase‖ = 1)
    ∧ (∀ A : NamedAnyon,
      monodromy (namedAnyonModel A).exchangePhase =
        (namedAnyonModel A).monodromyPhase)
    ∧ (∀ m : ℕ, 2 ≤ m →
      IsAnyonic (namedAnyonModel (NamedAnyon.laughlinQuasihole m)).exchangePhase)
    ∧ (∀ m : ℕ, 2 ≤ m →
      (namedAnyonModel (NamedAnyon.laughlinQuasihole m)).exchangePhase ≠ 1
        ∧ (namedAnyonModel (NamedAnyon.laughlinQuasihole m)).exchangePhase ≠ -1)
    ∧ (∀ k : ℕ, ∀ a : Fin k,
      (abelianWilsonAnyonModel k a).topologicalSpin =
        ribbonTwist (abelianWilsonAnyonModel k a).conformalWeight)
    ∧ (∀ k : ℕ, 0 < k → ∀ a b : Fin k,
      (abelianWilsonAnyonModel k a).braidingPhase b =
        (Real.sqrt k : ℂ) * (starRingEnd ℂ) (cswSMatrix k a b))
    ∧ semionAnyonModel.exchangePhase ≠ 1
    ∧ semionAnyonModel.exchangePhase ≠ -1
    ∧ semionAnyonModel.monodromyPhase = -1
    ∧ IsAnyonic semionAnyonModel.exchangePhase
    ∧ 1 < (namedAnyonModel NamedAnyon.isingSigma).quantumDimension
    ∧ (namedAnyonModel NamedAnyon.isingSigma).fusionChannelCount = 2
    ∧ (namedAnyonModel NamedAnyon.isingPsi).exchangePhase = -1
    ∧ (namedAnyonModel NamedAnyon.isingVacuum).exchangePhase = 1
    ∧ (namedAnyonModel NamedAnyon.halperin331Layer).chargeUnits = 1 / 4
    ∧ 2 * Real.pi * (namedAnyonModel NamedAnyon.halperin331Layer).conformalWeight =
      halperinSelfStatisticsAngle 3 1
    ∧ HasHalfFillingSemionChernSimonsBridge
    ∧ HasHalperin331KMatrixDerivation

/-- The generated anyon model layer is checked from the existing FQHE,
Chern--Simons Wilson-loop, ribbon, Ising, and Halperin K-matrix theorems. -/
lemma dataDrivenAnyonModels_checked : HasDataDrivenAnyonModels := by
  rcases semionAnyonModel_not_boson_fermion with ⟨hSemionBoson, hSemionFermion⟩
  exact ⟨namedAnyonModel_exchange_eq_ribbonTwist,
    namedAnyonModel_monodromy_eq_exchange_sq,
    namedAnyonModel_exchange_unit,
    namedAnyonModel_monodromy_eq_exchangeSpectrum,
    laughlinAnyonModel_isAnyonic,
    laughlinAnyonModel_genuinely_anyonic,
    abelianWilsonAnyonModel_topologicalSpin_eq_ribbon,
    abelianWilsonAnyonModel_braiding_eq_S,
    hSemionBoson,
    hSemionFermion,
    semionAnyonModel_monodromy,
    semionAnyonModel_isAnyonic,
    isingSigmaAnyonModel_nonabelian,
    isingSigmaAnyonModel_fusionChannelCount,
    isingPsiAnyonModel_fermion_phase,
    isingVacuumAnyonModel_boson_phase,
    halperin331LayerAnyonModel_charge,
    halperin331LayerAnyonModel_selfStatistics,
    halfFilling_semion_csw_bridge_checked,
    halperin331_kmatrix_derivation_checked⟩


/-- The repository's complete FQHE core capability: filling arithmetic, Jain
sequence, quantized Hall conductance, CSW torus degeneracy, abelian anyons,
semion/CSW bridge, charge-statistics, bulk-edge response, Pfaffian non-abelian
data, and the two-component `(3,3,1)` K-matrix discriminators are all available
together. -/
def HasFQHECoreFormalization : Prop :=
  laughlinFilling 2 = 1 / 2
    ∧ jainFilling 1 1 = 1 / 3
    ∧ hallConductanceUnits (1 / 2) = 1 / 2
    ∧ hallResistivityUnits (1 / 2) = 2
    ∧ Module.finrank ℂ (TorusHilbert 2) = 2
    ∧ HasHalfFillingSemionChernSimonsBridge
    ∧ HasAbelianAnyonSector 2 (by norm_num)
    ∧ laughlinAnyonPhase 2 ≠ 1
    ∧ laughlinAnyonPhase 2 ≠ -1
    ∧ laughlinStatisticalAngle 2 = Real.pi * laughlinQuasiholeCharge 2
    ∧ HasDataDrivenAnyonModels
    ∧ HasHalfFillingBulkEdgeResponse
    ∧ HasHalfFillingCandidateDiscriminators

/-- The full FQHE core bundle is checked without importing tables or adding new
axioms: it is assembled from the proved arithmetic, Chern--Simons, anyon, and
bulk-edge candidate-discriminator lemmas in this file. -/
lemma fqhe_core_formalization_checked : HasFQHECoreFormalization := by
  rcases laughlinAnyon_semion_not_boson_fermion with ⟨hnotBoson, hnotFermion⟩
  exact ⟨laughlin_two_is_half,
    jain_one_one_third,
    halfFilling_hallConductance,
    halfFilling_hallResistivity,
    halfFilling_abelian_torus_degeneracy,
    halfFilling_semion_csw_bridge_checked,
    halfFilling_abelian_anyon_sector,
    hnotBoson,
    hnotFermion,
    charge_statistics_relation 2,
    dataDrivenAnyonModels_checked,
    halfFilling_bulkEdgeResponse_checked,
    halfFilling_candidate_discriminators_checked⟩


/-- The Laughlin/FQHE topological order uses the repository's CSW item-9
package: Poisson-resummed theta modularity, Verlinde fusion, Wilson-operator
diagonalization, geometric-quantization dimension, Wilson braiding as the
normalized `S`-matrix, `S`-unitarity, `S`-symmetry, and `S² = C`. -/
def HasLaughlinCSWModularData (k : ℕ) (hk : 0 < k) : Prop :=
  (∀ τ z a,
    cswThetaBasis k a (-1 / τ) z =
      ∑ b : Fin k, cswSMatrix k a b * cswThetaBasis k b τ z)
    ∧ (∀ a b c,
      cswFusionCoeff k a b c = cswVerlindeCoefficientByS k hk a b c)
    ∧ (∀ a q,
      cswWilsonVerlindeOperator k a (fun b => cswSMatrix k b q) =
        fun c => cswVerlindeEigenvalue k hk a q * cswSMatrix k c q)
    ∧ Module.finrank ℂ (TorusHilbert k) = Fintype.card (Fin k)
    ∧ (∀ a b : Fin k,
      wilsonBraidingPhase k a b =
        (Real.sqrt k : ℂ) * (starRingEnd ℂ) (cswSMatrix k a b))
    ∧ (∀ a b : Fin k,
      (∑ c : Fin k, cswSMatrix k a c * (starRingEnd ℂ) (cswSMatrix k b c))
        = if a = b then 1 else 0)
    ∧ (∀ a b : Fin k, cswSMatrix k a b = cswSMatrix k b a)
    ∧ (∀ a b : Fin k,
      (∑ c : Fin k, cswSMatrix k a c * cswSMatrix k c b)
        = if (k : ℤ) ∣ ((a.val : ℤ) + (b.val : ℤ)) then 1 else 0)

/-- Once the already-explicit CSW geometric-quantization package is supplied,
the Laughlin/FQHE modular data is a direct consequence of existing CSW, Wilson,
and Verlinde theorems. -/
lemma laughlin_csw_modular_data_checked (k : ℕ) (hk : 0 < k)
    (G : CSWGeometricQuantizationPackage k hk) :
    HasLaughlinCSWModularData k hk := by
  rcases csw_item9_verlinde_geometric_quantization k hk G with
    ⟨hTheta, hVerlinde, hWilson, hDim⟩
  exact ⟨hTheta,
    hVerlinde,
    hWilson,
    hDim,
    fun a b => wilsonBraidingPhase_eq_S k hk a b,
    fun a b => cswSMatrix_unitary k hk a b,
    fun a b => cswSMatrix_symm k a b,
    fun a b => cswSMatrix_sq_eq_chargeConjugation k hk a b⟩

/-- At `ν = 1/2`, the `U(1)₂` semion fuses with itself to the vacuum charge. -/
lemma halfFilling_semion_fusion_to_vacuum :
    cswFusionCoeff 2 semionCharge semionCharge (cswZeroCharge 2 (by norm_num)) = 1 := by
  apply cswFusionCoeff_eq_one_of_dvd
  norm_num [semionCharge, cswZeroCharge]

/-- The Wilson/Verlinde operator for the semion sends the semion basis vector
to the vacuum component with coefficient `1`: the operator form of
`semion ⊗ semion = vacuum`. -/
lemma halfFilling_semionWilson_squares_to_vacuum :
    cswWilsonVerlindeOperator 2 semionCharge (cswChargeBasis 2 semionCharge)
      (cswZeroCharge 2 (by norm_num)) = 1 := by
  rw [cswWilsonVerlindeOperator_basis]
  simpa using halfFilling_semion_fusion_to_vacuum

/-- Complete half-filling topological-order capability: the core FQHE sector,
bulk-edge response, CSW item-9 modular data, and explicit semion fusion are
available together. The remaining analytic content needed to prove this bundle
is precisely the already named `CSWGeometricQuantizationPackage`, not a hidden
or duplicated axiom. -/
def HasHalfFillingCompleteTopologicalOrder : Prop :=
  HasFQHECoreFormalization
    ∧ HasHalfFillingBulkEdgeResponse
    ∧ HasLaughlinCSWModularData 2 (by norm_num)
    ∧ cswFusionCoeff 2 semionCharge semionCharge (cswZeroCharge 2 (by norm_num)) = 1
    ∧ cswWilsonVerlindeOperator 2 semionCharge (cswChargeBasis 2 semionCharge)
      (cswZeroCharge 2 (by norm_num)) = 1

/-- The complete half-filling FQHE topological-order bundle is checked by
combining the local FQHE theorems with the repository's CSW modular/Verlinde
package. -/
lemma halfFilling_completeTopologicalOrder_checked
    (G : CSWGeometricQuantizationPackage 2 (by norm_num)) :
    HasHalfFillingCompleteTopologicalOrder :=
  ⟨fqhe_core_formalization_checked,
    halfFilling_bulkEdgeResponse_checked,
    laughlin_csw_modular_data_checked 2 (by norm_num) G,
    halfFilling_semion_fusion_to_vacuum,
    halfFilling_semionWilson_squares_to_vacuum⟩

end Physlib.QuantumMechanics.ComplexAction.FractionalQuantumHallHalfFilling

end

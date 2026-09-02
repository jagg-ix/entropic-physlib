/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Curvature.JacobiRicciBianchiTetrad
public import Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor

/-!
# Babourova–Frolov: dilatonic charge in a Weyl–Cartan space

Babourova and Frolov (1998) study a perfect **dilaton-spin fluid** and a test particle with spin and
dilatonic charge in a **Weyl–Cartan space** `Y₄`: a metric-affine space whose nonmetricity
`Q_αβ = −Dg_αβ` is *pure trace* (Weyl), `Q_αβ = ¼ g_αβ Q` (Eq. A.4).

The Weyl–Cartan connection is the repository's rigid **`TetradConnection`** (`Curvature.
JacobiRicciBianchiTetrad`, `Γ_abc = −Γ_bac`, i.e. *metric-compatible*) **plus a distortion** `Δ` that
carries the nonmetricity — dropping the antisymmetry is exactly what makes the space non-metric.

* **§A — the nonmetricity of the Weyl–Cartan connection** (reusing `TetradConnection`). `nonmetricity`
  is the symmetric part `Q_abc = −(Γ_abc + Γ_bac)`; a rigid `TetradConnection` is metric-compatible
  (`tetradConnection_metricCompatible`, `Q = 0`), and the Weyl–Cartan connection `°Γ + Δ` has its
  nonmetricity carried entirely by the distortion (`weylCartanConnection_nonmetricity`, Eq. A.5). The
  explicit distortion `Δ_abc = −⅛ g_ab Q_c` produces the Weyl nonmetricity
  (`weylDistortion_isWeylNonmetricity`, `weylCartan_connection_isWeyl`), whose metric trace is the
  Weyl one-form (`weylOneForm_eq_nonmetricityTrace`, the `¼` fixed by `gᵃᵇg_αβ = 4`).
* **§B — the homothetic (Weyl segmental) curvature** (reusing `RiemannTensor` / `IsRiemannCurvature`).
  `homotheticCurvature` is the first-pair trace `Rᵃ_αcd`; it **vanishes for a metric-compatible
  (Riemann–Cartan) curvature** (`homotheticCurvature_zero_of_metricCompatible`, from
  `antisymm_left`) and is **antisymmetric** (a two-form, `homotheticCurvature_antisymm`). So the
  dilatonic field strength `Rᵃ_α = ½ dQ` (Eq. A.8) is nonzero *only* with nonmetricity. The curvature
  itself splits (Eq. A.6) into nonmetric (homothetic) and Riemann–Cartan parts
  (`curvature_weylCartan_decomposition`), the nonmetric part vanishing for a metric-compatible
  curvature (`curvatureNonmetricPart_zero_of_metricCompatible`).
* **§C — the test-particle motion (Eq. 3.2) and Corollaries 1–3.** The force splits into geodesic,
  Mathisson (spin), torsion, and Weyl (dilatonic) parts (`testParticleForce`). Setting the couplings
  to zero reduces the motion: `corollary1_riemann` (`S = J = 0`: Riemann geodesic), `corollary2_
  riemannCartan` (`J = 0`: Riemann–Cartan), `weylForce_zero_of_no_dilatonicCharge` (Corollary 3:
  `J = 0` matter feels no Weyl force).
* **§D — the dilaton-spin fluid is isentropic** (Eqs. 2.7–2.8): energy conservation along a streamline
  plus the first law force `ds = 0` (`streamline_isentropic`).

**Honest layering.** Proven: the connection nonmetricity (from `TetradConnection`), the homothetic
curvature vanishing under metric compatibility (from `IsRiemannCurvature`), the observability
corollary, and the isentropy. Not formalized: the full form-valued equations of motion (Eqs. 2.1–3.2)
needing exterior/interior-product calculus. **Note:** this "Weyl" is Hermann Weyl's nonmetricity/
dilation geometry, not the Weyl *conformal curvature* tensor of `Curvature.WeylTensorTraceFree`.

## References

* O. V. Babourova, B. N. Frolov, "Perfect fluid and test particle with spin and dilatonic charge in a
  Weyl-Cartan space", Mod. Phys. Lett. A **13**, 7 (1998) [`Babourova:1998ah`], Eqs. (2.7), (2.8),
  (3.2), Corollary 3, Appendix (A.1)–(A.8). Reuses `Curvature.JacobiRicciBianchiTetrad`
  (`TetradConnection`) and `Curvature.RiemannCurvatureTensor` (`RiemannTensor`, `IsRiemannCurvature`).


-/

set_option autoImplicit false

open scoped BigOperators

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.WeylCartanDilatonicCharge

open Physlib.QuantumMechanics.ComplexAction.Curvature.JacobiRicciBianchiTetrad
open Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor

variable {ι : Type*}


/-- **The nonmetricity** of a (fully lowered) connection `Q_abc = −(Γ_abc + Γ_bac)` — the symmetric
part of the connection, the failure of metric compatibility `Dg = 0` (Babourova–Frolov Eq. A.1). -/
def nonmetricity (Γ : ι → ι → ι → ℝ) (a b c : ι) : ℝ := -(Γ a b c + Γ b a c)

/-- **A rigid `TetradConnection` is metric-compatible** (`Q = 0`): the orthonormal-tetrad antisymmetry
`Γ_abc = −Γ_bac` is exactly the vanishing of the nonmetricity — the Riemann–Cartan (torsion, no
nonmetricity) case. -/
lemma tetradConnection_metricCompatible (T : TetradConnection ι) (a b c : ι) :
    nonmetricity T.Γ a b c = 0 := by
  unfold nonmetricity; have := T.rigid a b c; linarith

/-- **The Weyl–Cartan connection `°Γ + Δ` has its nonmetricity carried by the distortion `Δ`**
(Babourova–Frolov Eq. A.5): the rigid Riemann–Cartan part `°Γ` contributes nothing, so all the
nonmetricity comes from the Weyl distortion. -/
lemma weylCartanConnection_nonmetricity (T : TetradConnection ι) (Δ : ι → ι → ι → ℝ) (a b c : ι) :
    nonmetricity (fun a b c => T.Γ a b c + Δ a b c) a b c = nonmetricity Δ a b c := by
  unfold nonmetricity; have := T.rigid a b c; linarith

/-- **The Weyl–Cartan pure-trace nonmetricity constraint** `Q_abc = ¼ g_ab Q_c` (Eq. A.4): the
nonmetricity is a pure trace, with `Q_c` the Weyl one-form. -/
def IsWeylNonmetricity (Q : ι → ι → ι → ℝ) (g : ι → ι → ℝ) (weyl : ι → ℝ) : Prop :=
  ∀ a b c, Q a b c = (1 / 4) * g a b * weyl c

/-- **The Weyl one-form is the metric trace of the nonmetricity** `gᵃᵇ Q_abc = Q_c`, the `¼` fixed by
the dimension `gᵃᵇg_ab = 4`. -/
lemma weylOneForm_eq_nonmetricityTrace [Fintype ι] (Q : ι → ι → ι → ℝ) (g ginv : ι → ι → ℝ)
    (weyl : ι → ℝ) (h : IsWeylNonmetricity Q g weyl)
    (hdim : ∑ a, ∑ b, ginv a b * g a b = 4) (c : ι) :
    ∑ a, ∑ b, ginv a b * Q a b c = weyl c := by
  calc ∑ a, ∑ b, ginv a b * Q a b c
      = ∑ a, ∑ b, (1 / 4 * weyl c) * (ginv a b * g a b) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [h a b c]; ring
    _ = (1 / 4 * weyl c) * ∑ a, ∑ b, ginv a b * g a b := by simp_rw [← Finset.mul_sum]
    _ = weyl c := by rw [hdim]; ring

/-- **The explicit Weyl distortion** `Δ_abc = −⅛ g_ab Q_c` (Babourova–Frolov Eq. A.5, the pure-trace
part of the distortion). -/
noncomputable def weylDistortion (g : ι → ι → ℝ) (weyl : ι → ℝ) (a b c : ι) : ℝ :=
  -(1 / 8) * g a b * weyl c

/-- **The Weyl distortion produces the Weyl nonmetricity** `Q_abc = ¼ g_ab Q_c` (Eq. A.5 ⟹ A.4). -/
lemma weylDistortion_isWeylNonmetricity (g : ι → ι → ℝ) (weyl : ι → ℝ)
    (hsym : ∀ a b, g a b = g b a) :
    IsWeylNonmetricity (nonmetricity (weylDistortion g weyl)) g weyl := by
  intro a b c; unfold nonmetricity weylDistortion; rw [hsym b a]; ring

/-- **The full Weyl–Cartan connection `°Γ + Δ_Weyl` is a Weyl connection** — the rigid Riemann–Cartan
`TetradConnection` plus the explicit Weyl distortion has the pure-trace Weyl nonmetricity (Eq. A.5,
complete). -/
lemma weylCartan_connection_isWeyl (T : TetradConnection ι) (g : ι → ι → ℝ) (weyl : ι → ℝ)
    (hsym : ∀ a b, g a b = g b a) :
    IsWeylNonmetricity
      (nonmetricity (fun a b c => T.Γ a b c + weylDistortion g weyl a b c)) g weyl := by
  intro a b c
  rw [weylCartanConnection_nonmetricity T (weylDistortion g weyl)]
  exact weylDistortion_isWeylNonmetricity g weyl hsym a b c


/-- **The homothetic (Weyl segmental) curvature** `Rᵃ_αcd = gᵃᵉ R_eacd` — the first-pair trace of the
curvature, the dilation/scale part `Rᵃ_α = ½ dQ` that couples to the dilatonic charge (Eq. A.8). -/
noncomputable def homotheticCurvature [Fintype ι] (gInv : ι → ι → ℝ) (Rm : RiemannTensor ι)
    (c d : ι) : ℝ :=
  ∑ a, ∑ e, gInv a e * Rm e a c d

/-- **The homothetic curvature vanishes in a metric-compatible (Riemann–Cartan) space**: the first-
pair antisymmetry `R_eacd = −R_aecd` (`IsRiemannCurvature.antisymm_left`) forces `Rᵃ_αcd = 0`. So the
dilatonic field strength `Rᵃ_α = ½ dQ` is nonzero **only** where the nonmetricity is — the geometric
core of Corollary 3. -/
lemma homotheticCurvature_zero_of_metricCompatible [Fintype ι] (gInv : ι → ι → ℝ)
    (Rm : RiemannTensor ι) (h : IsRiemannCurvature Rm) (hsym : ∀ a e, gInv a e = gInv e a) (c d : ι) :
    homotheticCurvature gInv Rm c d = 0 := by
  unfold homotheticCurvature
  have step : (∑ a, ∑ e, gInv a e * Rm e a c d) = ∑ a, ∑ e, -(gInv e a * Rm a e c d) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => ?_
    rw [hsym a e, show Rm e a c d = - Rm a e c d from by have := h.antisymm_left a e c d; linarith]
    ring
  have step2 : (∑ a, ∑ e, -(gInv e a * Rm a e c d)) = -(∑ a, ∑ e, gInv a e * Rm e a c d) := by
    simp only [Finset.sum_neg_distrib]; congr 1; exact Finset.sum_comm
  rw [step, step2] at *; linarith [step]

/-- **The dilatonic field strength is a two-form** (antisymmetric) `Rᵃ_αcd = −Rᵃ_αdc`, like the
electromagnetic Faraday tensor — consistent with `Rᵃ_α = ½ dQ` being the exterior derivative of the
Weyl one-form (Eq. A.8), from `IsRiemannCurvature.antisymm_right`. -/
lemma homotheticCurvature_antisymm [Fintype ι] (gInv : ι → ι → ℝ) (Rm : RiemannTensor ι)
    (h : IsRiemannCurvature Rm) (c d : ι) :
    homotheticCurvature gInv Rm c d = - homotheticCurvature gInv Rm d c := by
  unfold homotheticCurvature
  rw [show (∑ a, ∑ e, gInv a e * Rm e a d c) = ∑ a, ∑ e, -(gInv a e * Rm e a c d) from
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun e _ => by
      rw [show Rm e a d c = - Rm e a c d from by have := h.antisymm_right e a c d; linarith]; ring]
  simp only [Finset.sum_neg_distrib, neg_neg]

/-- **The nonmetric (homothetic) part of the curvature** `R_(ab)cd = ½(R_abcd + R_bacd)` — the
first-pair symmetric part, the segmental `⅛ δ dQ` piece of Eq. A.6 that a metric-compatible curvature
lacks. -/
noncomputable def curvatureNonmetricPart (Rm : RiemannTensor ι) (a b c d : ι) : ℝ :=
  (1 / 2) * (Rm a b c d + Rm b a c d)

/-- **The Riemann–Cartan part of the curvature** `R_[ab]cd = ½(R_abcd − R_bacd)` — the first-pair
antisymmetric part, the `°R + P` of Eq. A.6. -/
noncomputable def curvatureRiemannCartanPart (Rm : RiemannTensor ι) (a b c d : ι) : ℝ :=
  (1 / 2) * (Rm a b c d - Rm b a c d)

/-- **The Weyl–Cartan curvature decomposition** (Babourova–Frolov Eq. A.6): every curvature splits into
its nonmetric (homothetic) and Riemann–Cartan parts — the curvature analogue of the connection split
`Γ = °Γ + Δ` (Eq. A.5). -/
lemma curvature_weylCartan_decomposition (Rm : RiemannTensor ι) (a b c d : ι) :
    Rm a b c d = curvatureNonmetricPart Rm a b c d + curvatureRiemannCartanPart Rm a b c d := by
  unfold curvatureNonmetricPart curvatureRiemannCartanPart; ring

/-- The Riemann–Cartan part is first-pair antisymmetric (metric-compatible). -/
lemma curvatureRiemannCartanPart_antisymm (Rm : RiemannTensor ι) (a b c d : ι) :
    curvatureRiemannCartanPart Rm a b c d = - curvatureRiemannCartanPart Rm b a c d := by
  unfold curvatureRiemannCartanPart; ring

/-- **A metric-compatible curvature has no nonmetric part** (`dQ = 0`): the segmental/homothetic piece
of Eq. A.6 vanishes, leaving pure Riemann–Cartan curvature — from `antisymm_left`. -/
lemma curvatureNonmetricPart_zero_of_metricCompatible (Rm : RiemannTensor ι)
    (h : IsRiemannCurvature Rm) (a b c d : ι) : curvatureNonmetricPart Rm a b c d = 0 := by
  unfold curvatureNonmetricPart; have := h.antisymm_left a b c d; linarith


/-- **The Mathisson (spin-curvature) force** `∝ S · R` (Eq. 3.1, the third term): the spin `S` coupled
to the curvature. -/
noncomputable def mathissonForce (spin curvature : ℝ) : ℝ := -(1 / 2) * spin * curvature

/-- **The test-particle Weyl force** (Eq. 3.2): Lorentz-like `¹⁄₁₆ J · F` with the dilatonic charge `J`
and the homothetic curvature `F = Rᵃ_α = ½ dQ` as dilatonic field strength. -/
noncomputable def weylForce (dilatonicCharge fieldStrength : ℝ) : ℝ :=
  (1 / 16) * dilatonicCharge * fieldStrength

/-- **The total test-particle force** (Eq. 3.2) is the sum of the geodesic, Mathisson (spin),
torsion (translational), and Weyl (dilatonic) contributions. -/
def testParticleForce (geodesic mathisson torsion weyl : ℝ) : ℝ :=
  geodesic + mathisson + torsion + weyl

/-- **Corollary 3 — the Weyl structure is unobservable without dilatonic charge.** A test particle
with `J = 0` feels no Weyl force, whatever the field strength: "usual" matter cannot detect the Weyl
structure of spacetime. -/
lemma weylForce_zero_of_no_dilatonicCharge (F : ℝ) : weylForce 0 F = 0 := by
  simp [weylForce]

/-- **Corollary 2 — spin without dilatonic charge: Riemann–Cartan motion.** With `J = 0` the Weyl
force vanishes, leaving the geodesic, Mathisson (spin) and torsion terms — the motion in a
Riemann–Cartan space. -/
lemma corollary2_riemannCartan (geodesic mathisson torsion F : ℝ) :
    testParticleForce geodesic mathisson torsion (weylForce 0 F)
      = geodesic + mathisson + torsion := by
  simp [testParticleForce, weylForce]

/-- **Corollary 1 — no spin, no dilatonic charge: Riemann geodesic.** With `S = 0` (no Mathisson
force), `J = 0` (no Weyl force), and no torsion, the test particle follows the Riemann geodesic. -/
lemma corollary1_riemann (geodesic C F : ℝ) :
    testParticleForce geodesic (mathissonForce 0 C) 0 (weylForce 0 F) = geodesic := by
  simp [testParticleForce, mathissonForce, weylForce]


/-- **The perfect dilaton-spin fluid is isentropic** (Eqs. 2.7–2.8): energy conservation along a
streamline `dε = (ε+p)/n dn`, compared with the first thermodynamic principle
`dε = T ds + (ε+p)/n dn`, forces `T ds = 0`; with `T ≠ 0`, `ds = 0`. -/
lemma streamline_isentropic (ε p n dn dε ds T : ℝ) (hT : T ≠ 0)
    (hStreamline : dε = (ε + p) / n * dn)
    (hFirstLaw : dε = T * ds + (ε + p) / n * dn) :
    ds = 0 := by
  have hTds : T * ds = 0 := by rw [hStreamline] at hFirstLaw; linarith
  exact (mul_eq_zero.mp hTds).resolve_left hT

end Physlib.QuantumMechanics.ComplexAction.WeylCartanDilatonicCharge

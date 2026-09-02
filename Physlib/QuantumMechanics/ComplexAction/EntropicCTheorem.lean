/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.Calculus.Deriv.MeanValue
/- ZIL-BEGIN -/
public meta import Zil
/- ZIL-END -/

/-!
# The entropic c-theorem: the entanglement-entropy c-function decreases under RG (Casini–Huerta)

Formalizes the calculus core of the **entropic c-theorem** of H. Casini & M. Huerta, *A finite
entanglement entropy and the c-theorem*, Phys. Lett. B 600 (2004) 142 (hep-th/0405111). For a single
interval of size `r` in a `1+1`-dimensional QFT the finite (regularized) geometric entropy `G(r)`
(Eq 16) is severely constrained by **strong subadditivity** (SSA) plus Poincaré invariance:

* `S(A) + S(B) ≥ S(A∩B) + S(A∪B)`   (SSA, Eq 2),
* which for equal-size intersecting diamonds gives `G(√(r₁r₂)) ≥ ½(G(r₁) + G(r₂))` (Eq 19), i.e.
  **`Ḡ(a) := G(eᵃ)` is concave** in the logarithmic length `a = log r` (`Ḡ'' ≤ 0`, Eq 22).

The paper's **c-function** is `C(r) ≡ r G'(r)` (Eq 23). In the logarithmic variable this is exactly the
derivative `C = Ḡ'(a)` (chain rule: `Ḡ'(a) = eᵃ G'(eᵃ) = r G'(r)`), so the two constraints read

* `C(r) = r G'(r) ≥ 0`             (Eq 23, `G` increasing),
* `C'(r) = G'(r) + r G''(r) ≤ 0`   (Eq 24) — **`C` is non-increasing**, the entropic c-theorem.

Here we carry the second (headline) inequality: SSA-concavity of `Ḡ` (`deriv (deriv Ḡ) ≤ 0`) forces the
c-function `C = Ḡ'` to be **antitone** (`entropicCTheorem`), so it decreases monotonically from the UV to
the IR (`entropicCentralCharge_UV_ge_IR`). At a conformal fixed point `Ḡ(a) = k·a + β`
(`cftLogLengthEntropy`, from `S = (1/6)(c+c̄) log(r/ε)`, Eq 34), the c-function is the **constant central
charge** `C = k = (c+c̄)/6` (`entropicCentralCharge_fixedPoint`,
`entropicCentralCharge_eq_centralCharge`) — stationary under RG, the entropic form of Zamolodchikov's
theorem.

The c-function measures the *running of the geometric entropy with the size of the traced-out region*:
it is the RG-scale counterpart of the entropic-time program's entropy-production monotonicity. It attaches
to the exactly-solvable density region `S = log deg` (`PermutationInvariantEntanglementEntropy`) — that
`log deg` is the fixed-point value the running c-function interpolates between — and to the first-law /
horizon-entropy arc (the paper's stated aim was the entropy–gravity relation).

* **§A — the fixed-point entropy and its c-function.** `cftLogLengthEntropy`,
  `cftLogLengthEntropy_deriv` (`Ḡ'(a) = k`), `entropicCentralCharge`, `entropicCentralCharge_fixedPoint`
  (`C = k`), `entropicCentralCharge_eq_centralCharge` (`C = (c+c̄)/6`).
* **§B — the c-theorem.** `entropicCTheorem` (SSA-concavity ⟹ `C` antitone),
  `entropicCentralCharge_UV_ge_IR` (`C_IR ≤ C_UV`).

## References

* H. Casini, M. Huerta, *A finite entanglement entropy and the c-theorem*, Phys. Lett. B 600 (2004) 142,
  hep-th/0405111 — Eqs (16), (19)–(24), (34); §2.2.
* A. B. Zamolodchikov, *Irreversibility of the flux of the renormalization group in a 2D field theory*,
  JETP Lett. 43 (1986) 730 — the original c-theorem.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.EntropicCTheorem

/-! ### §A — the fixed-point entropy and its c-function -/

/-- The **fixed-point geometric entropy in the logarithmic length** `Ḡ(a) = G(eᵃ) = k·a + β`, from the
CFT interval entropy `S = k log(r/ε) + β` with `k = (c+c̄)/6` (Casini–Huerta Eqs 16, 34; `a = log r`). -/
noncomputable def cftLogLengthEntropy (k β : ℝ) : ℝ → ℝ := fun a => k * a + β

/-- The fixed-point entropy has constant slope `Ḡ'(a) = k`. -/
lemma cftLogLengthEntropy_hasDerivAt (k β a : ℝ) :
    HasDerivAt (cftLogLengthEntropy k β) k a := by
  unfold cftLogLengthEntropy
  simpa using (hasDerivAt_id' (x := a) |>.const_mul k).add_const β

lemma cftLogLengthEntropy_deriv (k β a : ℝ) : deriv (cftLogLengthEntropy k β) a = k :=
  (cftLogLengthEntropy_hasDerivAt k β a).deriv

/-- The **entropic c-function** `C(r) = r G'(r)`, which in the logarithmic length `a = log r` is the
derivative `C = Ḡ'(a)` (Casini–Huerta Eq 23). -/
noncomputable def entropicCentralCharge (G : ℝ → ℝ) (a : ℝ) : ℝ := deriv G a

/-- **[c-function at a fixed point `C = k`]** at a conformal fixed point the c-function is the constant
`k` — stationary under the RG flow (the entropic Zamolodchikov theorem). -/
lemma entropicCentralCharge_fixedPoint (k β a : ℝ) :
    entropicCentralCharge (cftLogLengthEntropy k β) a = k :=
  cftLogLengthEntropy_deriv k β a

/-- **[c-function = central charge]** with `k = (c+c̄)/6` (Eq 34) the fixed-point c-function is exactly the
CFT central charge, `C = (c+c̄)/6`. -/
lemma entropicCentralCharge_eq_centralCharge (c cbar β a : ℝ) :
    entropicCentralCharge (cftLogLengthEntropy ((c + cbar) / 6) β) a = (c + cbar) / 6 :=
  entropicCentralCharge_fixedPoint ((c + cbar) / 6) β a

/-! ### §B — the c-theorem -/

/-- **[The entropic c-theorem]** strong subadditivity makes `Ḡ(a) = G(eᵃ)` concave in the logarithmic
length (`Ḡ'' ≤ 0`, Casini–Huerta Eqs 19–22), which forces the c-function `C = Ḡ'` to be **antitone**
(`C' = G' + r G'' ≤ 0`, Eq 24): the entanglement-entropy central charge decreases monotonically along the
renormalization-group flow. -/
lemma entropicCTheorem (G : ℝ → ℝ) (hdiff : Differentiable ℝ (deriv G))
    (hconc : ∀ a, deriv (deriv G) a ≤ 0) : Antitone (entropicCentralCharge G) := by
  unfold entropicCentralCharge
  exact antitone_of_deriv_nonpos hdiff hconc

/-- **[`C_IR ≤ C_UV`]** the c-function at a larger (infrared) scale never exceeds its value at a smaller
(ultraviolet) scale — the directed content of the c-theorem. -/
lemma entropicCentralCharge_UV_ge_IR (G : ℝ → ℝ) (hdiff : Differentiable ℝ (deriv G))
    (hconc : ∀ a, deriv (deriv G) a ≤ 0) {aUV aIR : ℝ} (h : aUV ≤ aIR) :
    entropicCentralCharge G aIR ≤ entropicCentralCharge G aUV :=
  entropicCTheorem G hdiff hconc h

/- ZIL-BEGIN -/

zil attach cftLogLengthEntropy_deriv where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.EntropicCTheorem.cftLogLengthEntropy_hasDerivAt",
  formalizes @ "claim:cft-fixed-point-log-length-entropy-has-constant-slope-k",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:the-linear-log-length-entropy-is-the-fixed-point-ansatz-not-a-derived-cft-partition-function"

zil attach entropicCentralCharge_fixedPoint where
  supported_by @ "lean:cftLogLengthEntropy_deriv",
  formalizes @ "claim:entropic-c-function-equals-constant-k-at-a-conformal-fixed-point-stationary-under-rg",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:stationarity-value-at-a-fixed-point-not-the-full-zamolodchikov-c-theorem-flow"

zil attach entropicCentralCharge_eq_centralCharge where
  formalizes @ "claim:entropic-c-function-fixed-point-value-is-the-cft-central-charge-c-plus-cbar-over-six",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:casini-huerta-2004-finite-entanglement-entropy-and-the-c-theorem",
  caveat @ "claim:identification-of-k-with-the-central-charge-via-eq-34-not-an-independent-derivation-of-the-cardy-formula"

zil attach entropicCTheorem where
  formalizes @ "claim:strong-subadditivity-concavity-of-log-length-entropy-forces-the-c-function-to-be-antitone-entropic-c-theorem",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:casini-huerta-2004-finite-entanglement-entropy-and-the-c-theorem",
  supported_by @ "lean:antitone_of_deriv_nonpos",
  caveat @ "claim:the-ssa-concavity-of-g-bar-is-taken-as-the-physical-hypothesis-strong-subadditivity-itself-not-proved-here"

zil attach entropicCentralCharge_UV_ge_IR where
  supported_by @ "lean:entropicCTheorem",
  formalizes @ "claim:entropic-central-charge-does-not-increase-from-uv-to-ir-c-ir-le-c-uv",
  epistemic_status @ "consistency-identity",
  requires @ "claim:strong-subadditivity-concavity-of-log-length-entropy-forces-the-c-function-to-be-antitone-entropic-c-theorem",
  caveat @ "claim:directed-monotonicity-along-the-rg-scale-not-a-statement-about-the-full-rg-trajectory-in-coupling-space"

zil_file_contract physlib.entropicCTheorem where
  promises "The calculus core of the entropic c-theorem (Casini-Huerta). In the logarithmic length a = log r the c-function C(r) = r G'(r) is the derivative C = Ḡ'(a); strong subadditivity makes Ḡ concave, forcing C to be antitone (entropicCTheorem) so the entanglement-entropy central charge decreases monotonically from the UV to the IR (entropicCentralCharge_UV_ge_IR). At a conformal fixed point Ḡ = k·a + β gives C = k = (c+c̄)/6 constant (entropicCentralCharge_fixedPoint, entropicCentralCharge_eq_centralCharge) -- the entropic form of the Zamolodchikov theorem. This is the RG-scale monotonicity dual to the entropic-time H-theorem's time-monotonicity."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.EntropicCTheorem.entropicCentralCharge",
    "lean:Physlib.QuantumMechanics.ComplexAction.EntropicCTheorem.cftLogLengthEntropy",
    "lean:antitone_of_deriv_nonpos"]
  forbids_substitutes ["deriving strong subadditivity itself -- SSA-concavity of the log-length entropy is the physical input hypothesis, not a theorem here",
    "claiming the full Zamolodchikov c-theorem in coupling space -- only the entropic c-function's scale monotonicity is formalized"]
  witnessed_by [cftLogLengthEntropy_deriv, entropicCentralCharge_fixedPoint,
    entropicCentralCharge_eq_centralCharge, entropicCTheorem, entropicCentralCharge_UV_ge_IR]

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.EntropicCTheorem

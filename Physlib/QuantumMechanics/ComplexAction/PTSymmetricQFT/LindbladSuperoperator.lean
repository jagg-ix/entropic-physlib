/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.FieldSuperoperator
meta import Zil

/-!
# Open-system superoperators: the Lindblad dissipator and the GKSL generator

Extends the field superoperator of `PTSymmetricQFT.FieldSuperoperator` from the closed-system (unitary)
adjoint action to the **open-system** generators. On a `*`-algebra of observables `A` (the operator
algebra) we build the **Heisenberg-picture Lindblad dissipator**

  `𝒟[L](Y) = L† Y L − ½ {L†L, Y}`   (`lindbladDissipator`),

a `ℂ`-linear superoperator on `A`, and the full **GKSL / Lindblad generator** `𝓛(Y) = −i[H, Y] + 𝒟[L](Y)`
(`gksGenerator`). These are the dual (Heisenberg) picture of physlib's Schrödinger-picture
`Lindblad.lindbladSingleJumpDissipator` `𝒟[L](ρ) = LρL† − ½{L†L, ρ}` — adjoint under the trace
`Tr(𝒟_H[L](Y) ρ) = Tr(Y 𝒟_S[L](ρ))`. Where physlib's Schrödinger dissipator is trace-preserving
(`trace_lindbladSingleJumpDissipator_eq_zero`), the Heisenberg one is **unital** (`lindbladDissipator_one`,
`𝒟[L](1) = 0`) — the dual conservation law.

The two structural facts the request asks for:

* **The generator is a `*`-compatible algebra derivation.** The closed-system `liouvilleGenerator` of
  `PTSymmetricQFT.FieldSuperoperator` is an **algebra derivation** (`liouvilleGenerator_leibniz`,
  `ad`-Leibniz). On a `*`-algebra the Heisenberg generator `−i[H, ·]` with self-adjoint `H` is moreover
  **`*`-compatible** (`heisenbergGenerator_star`): `(𝓛 Y)† = 𝓛(Y†)` — it maps observables to observables.
* **The dissipator is `*`-compatible** (`lindbladDissipator_star`) and unital (`lindbladDissipator_one`),
  so the **full GKSL generator preserves self-adjointness** (`gksGenerator_star`): a genuine
  (Hermiticity-preserving) open-system generator.

* **§A — the Lindblad dissipator** (`lindbladDissipator`, `lindbladDissipator_apply`,
  `lindbladDissipator_one`, `lindbladDissipator_star`).
* **§B — the Heisenberg / GKSL generator** (`heisenbergGenerator`, `heisenbergGenerator_leibniz`,
  `heisenbergGenerator_complex_decompose`, `heisenbergGenerator_star`, `gksGenerator`, `gksGenerator_apply`,
  `gksGenerator_star`).
* **§C — the closed-system generator on `K^form`** (`liouvilleGenerator_leibniz`,
  `realize_liouvilleGenerator_eq_heisenberg`). `liouvilleGenerator` is an algebra derivation, and its
  realization is the Heisenberg generator on the operator algebra.

## References

* G. Lindblad, *On the generators of quantum dynamical semigroups*, Commun. Math. Phys. 48 (1976) 119;
  V. Gorini, A. Kossakowski, E. C. G. Sudarshan, J. Math. Phys. 17 (1976) 821 (GKSL).
* Repo carriers: `PTSymmetricQFT.FieldSuperoperator` (`fieldAdjoint`, `liouvilleGenerator`,
  `quantumRealize`); `Lindblad.FullLindbladODE` (`lindbladSingleJumpDissipator`, the Schrödinger-picture
  dual, with `trace_lindbladSingleJumpDissipator_eq_zero`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.LindbladSuperoperator

open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.FormalFieldTheory
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.QuantumSymmetry
open Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.FieldSuperoperator


variable {A : Type*} [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

/-- **The Lindblad dissipator** `𝒟[L](Y) = L† Y L − ½{L†L, Y}` — the dissipative open-system superoperator
on observables (Heisenberg picture), a `ℂ`-linear endomorphism of the `*`-algebra `A`. -/
noncomputable def lindbladDissipator (L : A) : A →ₗ[ℂ] A :=
  (LinearMap.mulLeft ℂ (star L)).comp (LinearMap.mulRight ℂ L)
    - (1 / 2 : ℂ) • (LinearMap.mulLeft ℂ (star L * L) + LinearMap.mulRight ℂ (star L * L))

@[simp] lemma lindbladDissipator_apply (L Y : A) :
    lindbladDissipator L Y = star L * Y * L - (1 / 2 : ℂ) • (star L * L * Y + Y * (star L * L)) := by
  simp [lindbladDissipator, mul_assoc]

/-- **[Heisenberg unitality] `𝒟[L](1) = 0`.** The dissipator annihilates the identity — the Heisenberg-
picture dual of the trace preservation `Tr(𝒟_S[L](ρ)) = 0`
(`Lindblad.trace_lindbladSingleJumpDissipator_eq_zero`). -/
lemma lindbladDissipator_one (L : A) : lindbladDissipator L 1 = 0 := by
  rw [lindbladDissipator_apply]; simp only [mul_one, one_mul]; module

/-- **[`*`-compatibility] `(𝒟[L](Y))† = 𝒟[L](Y†)`.** The dissipator commutes with the adjoint, so it
**preserves self-adjointness** — it maps observables to observables. -/
lemma lindbladDissipator_star (L Y : A) :
    star (lindbladDissipator L Y) = lindbladDissipator L (star Y) := by
  simp only [lindbladDissipator_apply, star_sub, star_smul, star_add, star_mul, star_star,
    mul_assoc, RCLike.star_def, map_div₀, map_one, map_ofNat]
  abel


/-- **The Heisenberg generator** `−i[H, ·]` — the unitary (Hamiltonian) part of the open-system dynamics on
the `*`-algebra `A`. -/
noncomputable def heisenbergGenerator (H : A) : A →ₗ[ℂ] A :=
  (-Complex.I) • (LinearMap.mulLeft ℂ H - LinearMap.mulRight ℂ H)

@[simp] lemma heisenbergGenerator_apply (H Y : A) :
    heisenbergGenerator H Y = (-Complex.I) • (H * Y - Y * H) := by
  simp [heisenbergGenerator]

/-- **[Reversible + dissipative split] `𝓛_{H_R − iH_I} = −i[H_R, ·] − [H_I, ·]`.**
The Heisenberg generator of a complex Hamiltonian splits into the unitary
Hamiltonian part generated by `H_R` and the real-coefficient commutator generated
by `H_I`. -/
lemma heisenbergGenerator_complex_decompose (H_R H_I Y : A) :
    heisenbergGenerator (H_R - Complex.I • H_I) Y
      = -Complex.I • (H_R * Y - Y * H_R) - (H_I * Y - Y * H_I) := by
  rw [heisenbergGenerator_apply]
  have hc : (H_R - Complex.I • H_I) * Y - Y * (H_R - Complex.I • H_I)
      = (H_R * Y - Y * H_R) - Complex.I • (H_I * Y - Y * H_I) := by
    rw [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, smul_sub]; abel
  rw [hc, smul_sub, smul_smul,
    show -Complex.I * Complex.I = (1 : ℂ) by rw [neg_mul, Complex.I_mul_I, neg_neg], one_smul]

/-- **The Heisenberg generator is an algebra derivation** `−i[H, YZ] = (−i[H,Y])Z + Y(−i[H,Z])`. -/
lemma heisenbergGenerator_leibniz (H Y Z : A) :
    heisenbergGenerator H (Y * Z) = heisenbergGenerator H Y * Z + Y * heisenbergGenerator H Z := by
  simp only [heisenbergGenerator_apply, smul_mul_assoc, mul_smul_comm, ← smul_add]
  congr 1; noncomm_ring

/-- **[`*`-compatibility] For self-adjoint `H`, `(−i[H, Y])† = −i[H, Y†]`.** The Heisenberg generator with a
Hermitian Hamiltonian preserves self-adjointness — observables stay observables. -/
lemma heisenbergGenerator_star (H Y : A) (hH : star H = H) :
    star (heisenbergGenerator H Y) = heisenbergGenerator H (star Y) := by
  simp only [heisenbergGenerator_apply, star_smul, star_sub, star_mul, hH, RCLike.star_def,
    map_neg, Complex.conj_I]
  module

/-- **The GKSL / Lindblad generator** `𝓛(Y) = −i[H, Y] + 𝒟[L](Y)` — the full open-system generator (unitary
Hamiltonian part plus dissipator). -/
noncomputable def gksGenerator (H L : A) : A →ₗ[ℂ] A :=
  heisenbergGenerator H + lindbladDissipator L

lemma gksGenerator_apply (H L Y : A) :
    gksGenerator H L Y = heisenbergGenerator H Y + lindbladDissipator L Y := rfl

/-- **[`*`-compatibility] The GKSL generator preserves self-adjointness** (for self-adjoint `H`):
`(𝓛 Y)† = 𝓛(Y†)` — a genuine Hermiticity-preserving open-system generator. -/
lemma gksGenerator_star (H L Y : A) (hH : star H = H) :
    star (gksGenerator H L Y) = gksGenerator H L (star Y) := by
  rw [gksGenerator_apply, gksGenerator_apply, star_add, heisenbergGenerator_star H Y hH,
    lindbladDissipator_star]


variable {U : Type*} [AddCommGroup U] [Module ℂ U]

/-- **The Liouville generator is an algebra derivation** `𝓛_H(YZ) = 𝓛_H(Y)Z + Y 𝓛_H(Z)` on `K^form` — the
inner derivation `−i·ad_H` (`fieldAdjoint_leibniz` scaled). -/
lemma liouvilleGenerator_leibniz (H Y Z : KForm U) :
    liouvilleGenerator H (Y * Z) = liouvilleGenerator H Y * Z + Y * liouvilleGenerator H Z := by
  simp only [liouvilleGenerator_apply, smul_mul_assoc, mul_smul_comm, ← smul_add]
  congr 1; noncomm_ring

/-- **[Link] The realization of the Liouville generator is the Heisenberg generator** on the operator
algebra: `realize(𝓛_H(Y)) = −i[realize H, realize Y]`. So `liouvilleGenerator` on `K^form` and the
open-system `heisenbergGenerator` on `A` are the formula-side and operator-side faces of one generator. -/
lemma realize_liouvilleGenerator_eq_heisenberg (ev : U →ₗ[ℂ] A) (H Y : KForm U) :
    quantumRealize ev (liouvilleGenerator H Y)
      = heisenbergGenerator (quantumRealize ev H) (quantumRealize ev Y) := by
  rw [realize_liouvilleGenerator, heisenbergGenerator_apply]

end Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.LindbladSuperoperator

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.LindbladSuperoperator.lindbladDissipator_one where
  formalizes @ "claim:the-heisenberg-picture-lindblad-dissipator-annihilates-the-identity-observable-the-unitality-dual-to-trace-preservation-of-the-schrodinger-generator",
  supported_by @ "paper:gorini-kossakowski-sudarshan-lindblad-gksl-generator-of-a-quantum-dynamical-semigroup"

zil attach Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.LindbladSuperoperator.lindbladDissipator_star where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.LindbladSuperoperator.lindbladDissipator_apply",
  formalizes @ "claim:the-lindblad-dissipator-commutes-with-the-adjoint-so-it-preserves-self-adjointness-mapping-observables-to-observables"

zil attach Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.LindbladSuperoperator.heisenbergGenerator_complex_decompose where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.LindbladSuperoperator.heisenbergGenerator_apply",
  formalizes @ "claim:the-heisenberg-generator-of-a-complex-hamiltonian-h-r-minus-i-h-i-splits-into-the-unitary-reversible-commutator-generated-by-h-r-and-the-real-coefficient-dissipative-commutator-generated-by-h-i"

zil attach Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.LindbladSuperoperator.gksGenerator_star where
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.LindbladSuperoperator.lindbladDissipator_star",
  formalizes @ "claim:the-full-gksl-lindblad-generator-with-a-self-adjoint-hamiltonian-preserves-self-adjointness-a-genuine-hermiticity-preserving-open-system-generator",
  requires @ "claim:the-lindblad-dissipator-commutes-with-the-adjoint-so-it-preserves-self-adjointness-mapping-observables-to-observables"

zil_file_contract physlib.lindbladSuperoperator where
  promises "Extends the field superoperator from the closed-system unitary adjoint to the open-system GKSL generator on a star-algebra of observables. The Heisenberg-picture Lindblad dissipator D[L](Y) = L-dagger Y L - 1/2 {L-dagger L, Y} annihilates the identity (lindbladDissipator_one, the unitality dual to Schrodinger-picture trace preservation) and commutes with the adjoint, so it preserves self-adjointness -- observables stay observables (lindbladDissipator_star). The Heisenberg generator of a complex Hamiltonian H_R - i H_I splits into the unitary (reversible) commutator generated by H_R and the real-coefficient (dissipative) commutator generated by H_I (heisenbergGenerator_complex_decompose), and the full GKSL generator -i[H, .] + D[L] with self-adjoint H is Hermiticity-preserving (gksGenerator_star)."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.LindbladSuperoperator.lindbladDissipator",
    "lean:Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.LindbladSuperoperator.gksGenerator"]
  forbids_substitutes ["the complete-positivity of the generated semigroup and the GKSL structure theorem (that every such generator has this form), which are the cited open-quantum-systems infrastructure",
    "any claim about the dynamical semigroup's long-time behaviour, only the algebraic unitality, Hermiticity-preservation, and reversible/dissipative split are carried"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.LindbladSuperoperator.lindbladDissipator_one,
    Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.LindbladSuperoperator.lindbladDissipator_star,
    Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.LindbladSuperoperator.heisenbergGenerator_complex_decompose,
    Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.LindbladSuperoperator.gksGenerator_star]

/- ZIL-END -/

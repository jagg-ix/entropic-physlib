/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.GeometricAction
public import Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.CPTAntiunitary

/-!
# Greaves–Thomas §2.4: temporal orientation and the quantum action `[ρω]_q` (Wigner dichotomy)

Formalizes the part of §2.4 of *H. Greaves, T. Thomas, "The CPT Theorem"* (arXiv:1204.4674) that defines
the **quantum** geometric action `[ρω]_q`. The classical geometric action `[ρω]` of
`PTSymmetricQFT.GeometricAction` is `ℂ`-linear. The quantum action differs from it **exactly for those
`g ∈ G` with `ω(g)` time-reversing**: spacetime `M` has a *temporal orientation* that each `ω(g)`
either preserves or reverses, and — by **Wigner's theorem** — the Hilbert-space implementation `U(g)` of a
quantum symmetry is `ℂ`-linear (**unitary**) when `ω(g)` preserves time and `ℂ`-antilinear
(**antiunitary**) when `ω(g)` reverses it.

The bookkeeping is a single parity bit. Writing `θ(g) : Bool` for "does `ω(g)` reverse the temporal
orientation", the implementation `U(g)` is **`σ(g)`-semilinear** with the conjugation factor

  `σ(g) = conjFactor (θ g)`,   `conjFactor false = id` (unitary),   `conjFactor true = conj` (antiunitary).

Since `θ` is a homomorphism (`θ(gh) = θ(g) ⊕ θ(h)`) and `conj ∘ conj = id`, the conjugation factors compose
(`conjFactor_xor`): two antiunitaries make a unitary — exactly the structure behind `CPT`.

* **§A — temporal parity and the conjugation factor** (`conjFactor`, `conjFactor_false`, `conjFactor_true`,
  `conjFactor_xor`). The composition law `conjFactor (a ⊕ b) = conjFactor a ∘ conjFactor b` — time parities
  add, `antiunitary² = unitary`.
* **§B — the Wigner dichotomy** (`IsSemilinear`, `IsSemilinear.comp`, `conjFactor_dichotomy`). A symmetry
  implementation is `σ`-semilinear; semilinear maps compose with their factors composing; and every factor
  is either `id` (unitary) or `conj` (antiunitary).
* **§C — the quantum action `[ρω]_q`** (`QuantumImplementation`, `quantum_action_unitary`,
  `quantum_action_antiunitary`, `quantum_action_comp`). A quantum implementation assigns to each `g` a
  `conjFactor(θ g)`-semilinear `U(g)`; it is unitary (`= [ρω]`) for time-preserving `g` and **antiunitary**
  (`≠ [ρω]`) for time-reversing `g`; the implementations compose consistently with `θ`.
* **§D — the spacetime instances** (`parityOp_linear`, `timeReversal_antilinear`). Parity `P = γ⁰` is
  time-preserving, hence **linear/unitary**; time reversal `T = iγ¹γ³ψ*` is time-reversing, hence
  **antilinear/antiunitary** — its complex conjugation `ψ ↦ ψ*` is forced by Wigner. These are the `θ = false`
  and `θ = true` cases of `FirstQuantizedQED.CPTAntiunitary`.

## References

* H. Greaves, T. Thomas, *The CPT Theorem*, arXiv:1204.4674, §2.4 (the quantum action `[ρω]_q`, temporal
  orientation); E. P. Wigner, *Group Theory* (1959) — the unitary/antiunitary dichotomy.
* Repo dependencies: `PTSymmetricQFT.GeometricAction` (the classical action `[ρω]`); `FirstQuantizedQED.CPTAntiunitary`
  (`parityOp`, `timeReversal` — the spacetime `P`, `T`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.TemporalOrientation

open Matrix Complex
open spaceTime
open Physlib.QuantumMechanics.ComplexAction.FirstQuantizedQED.CPTAntiunitary

/-! ## §A — temporal-orientation parity and the conjugation factor -/

/-- **The conjugation factor of a temporal parity** `θ : Bool` (`false` = `ω(g)` preserves the temporal
orientation, `true` = reverses it). `conjFactor false = id` (the unitary case), `conjFactor true = conj`
(the antiunitary case). -/
def conjFactor (b : Bool) : ℂ →+* ℂ := if b then starRingEnd ℂ else RingHom.id ℂ

@[simp] theorem conjFactor_false : conjFactor false = RingHom.id ℂ := rfl
@[simp] theorem conjFactor_true : conjFactor true = starRingEnd ℂ := rfl

/-- **The conjugation factors compose** `conjFactor (a ⊕ b) = conjFactor a ∘ conjFactor b`. Time parities
add (`Bool.xor`); the `true ⊕ true = false` case is `conj ∘ conj = id` — **two antiunitaries make a
unitary**, the algebraic heart of `CPT`. -/
theorem conjFactor_xor (a b : Bool) :
    conjFactor (xor a b) = (conjFactor a).comp (conjFactor b) := by
  cases a <;> cases b <;> ext z <;> simp [conjFactor, Complex.conj_conj]

/-! ## §B — the Wigner dichotomy: semilinear implementations -/

/-- **A `σ`-semilinear map** `U(c • x) = σ(c) • U(x)` — `σ = id` is `ℂ`-linear (unitary), `σ = conj` is
`ℂ`-antilinear (antiunitary). -/
def IsSemilinear {H : Type*} [AddCommGroup H] [Module ℂ H] (σ : ℂ →+* ℂ) (U : H → H) : Prop :=
  ∀ (c : ℂ) (x : H), U (c • x) = σ c • U x

/-- **Semilinear maps compose, with their conjugation factors composing.** This is what makes the quantum
action a (projective) representation: `U(g) ∘ U(h)` includes the factor `σ(g) ∘ σ(h)`. -/
theorem IsSemilinear.comp {H : Type*} [AddCommGroup H] [Module ℂ H] {σ τ : ℂ →+* ℂ} {U V : H → H}
    (hU : IsSemilinear σ U) (hV : IsSemilinear τ V) : IsSemilinear (σ.comp τ) (U ∘ V) := by
  intro c x
  simp only [Function.comp_apply]
  rw [hV c x, hU (τ c) (V x), RingHom.comp_apply]

/-- **[Wigner] The dichotomy.** Every conjugation factor is either the identity (a **unitary**, `ℂ`-linear
implementation) or complex conjugation (an **antiunitary**, `ℂ`-antilinear implementation) — there is no
third option. -/
theorem conjFactor_dichotomy (b : Bool) :
    conjFactor b = RingHom.id ℂ ∨ conjFactor b = starRingEnd ℂ := by
  cases b <;> simp

/-! ## §C — the quantum action `[ρω]_q` -/

/-- **A quantum implementation of a symmetry group** (the quantum action `[ρω]_q`): to each `g` it assigns a
`conjFactor(θ g)`-semilinear implementation `U(g)` on the Hilbert space `H`, where `θ g` is the temporal
parity of `ω(g)` and `θ` is a homomorphism (`θ(gh) = θ(g) ⊕ θ(h)`). -/
structure QuantumImplementation (G H : Type*) [Group G] [AddCommGroup H] [Module ℂ H] where
  /-- The temporal parity of `ω(g)`. -/
  timeParity : G → Bool
  /-- `θ` is a homomorphism `G → ℤ/2`. -/
  timeParity_mul : ∀ g h, timeParity (g * h) = xor (timeParity g) (timeParity h)
  /-- The Hilbert-space implementation `U(g)`. -/
  U : G → (H → H)
  /-- Wigner: `U(g)` is semilinear with the conjugation factor of the temporal parity. -/
  semilinear : ∀ g, IsSemilinear (conjFactor (timeParity g)) (U g)

variable {G H : Type*} [Group G] [AddCommGroup H] [Module ℂ H]

/-- **[Greaves–Thomas] Time-preserving ⟹ unitary (the quantum action equals the classical one).** When
`ω(g)` preserves the temporal orientation, `U(g)` is `ℂ`-linear — `[ρω]_q(g) = [ρω](g)`. -/
theorem quantum_action_unitary (𝒰 : QuantumImplementation G H) (g : G)
    (hg : 𝒰.timeParity g = false) : IsSemilinear (RingHom.id ℂ) (𝒰.U g) := by
  have := 𝒰.semilinear g; rwa [hg, conjFactor_false] at this

/-- **[Greaves–Thomas] Time-reversing ⟹ antiunitary (the quantum action differs from the classical one).**
When `ω(g)` reverses the temporal orientation, `U(g)` is `ℂ`-antilinear — `[ρω]_q(g) ≠ [ρω](g)`. This is the
forced complex conjugation that distinguishes the quantum action. -/
theorem quantum_action_antiunitary (𝒰 : QuantumImplementation G H) (g : G)
    (hg : 𝒰.timeParity g = true) : IsSemilinear (starRingEnd ℂ) (𝒰.U g) := by
  have := 𝒰.semilinear g; rwa [hg, conjFactor_true] at this

/-- **[Greaves–Thomas] The quantum action composes consistently** `U(g) ∘ U(h)` is
`conjFactor(θ(gh))`-semilinear — the conjugation factors compose exactly as the temporal parities add, so
`[ρω]_q` is a (projective) representation. -/
theorem quantum_action_comp (𝒰 : QuantumImplementation G H) (g h : G) :
    IsSemilinear (conjFactor (𝒰.timeParity (g * h))) (𝒰.U g ∘ 𝒰.U h) := by
  rw [𝒰.timeParity_mul, conjFactor_xor]
  exact (𝒰.semilinear g).comp (𝒰.semilinear h)

/-! ## §D — the spacetime instances: `P` unitary, `T` antiunitary -/

/-- **[Greaves–Thomas + Wigner] Parity is time-preserving, hence linear/unitary.** `P ψ = γ⁰ ψ` is
`ℂ`-linear (`conjFactor false`) — `ω(P)` preserves the temporal orientation. -/
theorem parityOp_linear : IsSemilinear (conjFactor false) parityOp := by
  intro c ψ
  rw [conjFactor_false, RingHom.id_apply, parityOp, parityOp, Matrix.mulVec_smul]

/-- **[Greaves–Thomas + Wigner] Time reversal is time-reversing, hence antilinear/antiunitary.**
`T ψ = iγ¹γ³ ψ*` is `ℂ`-antilinear (`conjFactor true`) — `ω(T)` reverses the temporal orientation, and
Wigner's theorem *forces* the complex conjugation `ψ ↦ ψ*` that `FirstQuantizedQED.CPTAntiunitary.timeReversal`
records. -/
theorem timeReversal_antilinear : IsSemilinear (conjFactor true) timeReversal := by
  intro c ψ
  rw [conjFactor_true, timeReversal, timeReversal, star_smul, Matrix.mulVec_smul]
  rfl

end Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.TemporalOrientation

end

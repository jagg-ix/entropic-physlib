/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Moyal.OscillatorMatrixUnits
public import Physlib.QuantumMechanics.ComplexAction.Moyal.CollisionStar
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.RCLike.Basic
meta import Zil

/-!
# The Moyal integral as the faithful trace (Gayral et al., Lemma 2.1(v) and Theorem 2.2)

Completes the **Moyal integral** on the matricial model of the Moyal plane — the normalized
phase-space integral `(πθ)^{-N}∫ · d^{2N}x` of *Gayral–Gracia-Bondía–Iochum–Schücker–Várilly, "Moyal
Planes are Spectral Triples" (CMP 246, 2004)*, whose defining properties are Lemma 2.1(v) (the
tracial property `∫ f⋆g = ∫ g⋆f = ∫ f·g`) and Theorem 2.2 (`A_θ` is a Fréchet algebra *with a
distinguished faithful trace*).

On the oscillator eigentransition basis (`OscillatorMatrixUnits`, Gayral Lemma 2.4) the Moyal product
is the matrix-unit product, and the normalized integral is the **matrix trace**: `∫ f_{nn} = 1` on
every diagonal transition, `∫ f_{mn} = 0` off-diagonal (only the Gaussian-diagonal transitions carry
phase-space volume). All the analytic properties of the Moyal integral hold exactly:

* `moyalIntegral_moyalUnit` — the integral of an eigentransition is `δ_{mn}`.
* `moyalIntegral_tracial` — Lemma 2.1(v): `∫ f⋆g = ∫ g⋆f` (the tracial/cyclicity property).
* `moyalIntegral_collisionStar` / `moyalIntegral_moyalBracket` — **the integral annihilates the Moyal
  bracket**, `∫ {f,g}_MB = 0`: the phase-space integral of a Moyal bracket vanishes (closedness of
  the trace under the star-commutator — the reason expectation values are conserved by Moyal
  evolution), welded to the repository's Hiley Moyal bracket (`{·,·}_MB = (iℏ)⁻¹·[·,·]`).
* `moyalIntegral_faithful` — Theorem 2.2: the trace is **faithful**, `∫ f*⋆f = 0 ↔ f = 0`.
* `moyalIntegral_star` — reality: `∫ f* = conj ∫ f`.
* `moyalIntegral_one` — the volume of the truncated Moyal plane: `∫ 1 = d` (each oscillator level
  carries one unit of phase-space volume — the finite Weyl law).
-/

set_option autoImplicit false

open Matrix
open scoped ComplexOrder
open Physlib.QuantumMechanics.ComplexAction.Moyal.OscillatorMatrixUnits
open Physlib.QuantumMechanics.ComplexAction.Moyal.BakerOperatorSplit
open Physlib.QuantumMechanics.ComplexAction.CollisionOperatorSl2.CollisionModular

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Moyal.MoyalTraceIntegral

variable {d : ℕ}

/-- **The Moyal integral** `(πθ)^{-N}∫ · d^{2N}x` on the matricial model: the matrix trace. The
normalization absorbs the phase-space volume factor `(πθ)^N`, so each diagonal eigentransition
(Gaussian) integrates to `1`. -/
def moyalIntegral (F : Matrix (Fin d) (Fin d) ℂ) : ℂ := F.trace

/-- **The integral of an eigentransition is `δ_{mn}`** — only the diagonal (Gaussian) transitions
carry phase-space volume; every off-diagonal raising/lowering transition integrates to zero. -/
theorem moyalIntegral_moyalUnit (m n : Fin d) :
    moyalIntegral (moyalUnit m n) = if m = n then 1 else 0 := by
  unfold moyalIntegral moyalUnit
  by_cases h : m = n
  · subst h
    rw [Matrix.trace_single_eq_same, if_pos rfl]
  · rw [Matrix.trace_single_eq_of_ne (h := h), if_neg h]

/-- **[Gayral Lemma 2.1(v)] The tracial property** `∫ f⋆g = ∫ g⋆f`: the Moyal integral is cyclic
under the Moyal product — the property that makes it the distinguished trace of the Moyal algebra. -/
theorem moyalIntegral_tracial (F G : Matrix (Fin d) (Fin d) ℂ) :
    moyalIntegral (F * G) = moyalIntegral (G * F) :=
  Matrix.trace_mul_comm F G

/-- **The Moyal integral annihilates the star-commutator** `∫ [f,g]_⋆ = 0` — the closedness of the
trace: integrating a commutator over phase space gives zero. -/
theorem moyalIntegral_collisionStar (F G : Matrix (Fin d) (Fin d) ℂ) :
    moyalIntegral (collisionStar F G) = 0 := by
  unfold moyalIntegral collisionStar
  rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]

/-- **The Moyal integral annihilates the Moyal bracket** `∫ {f,g}_MB = 0` — the phase-space integral
of a Moyal bracket vanishes (welded to the repository's Hiley bracket `{·,·}_MB = (iℏ)⁻¹·[·,·]`).
This is why Moyal evolution `∂_t f = {H, f}_MB` conserves every expectation value `∫ f`: the
generator is integral-free. -/
theorem moyalIntegral_moyalBracket (ℏ : ℝ) (F G : Matrix (Fin d) (Fin d) ℂ) :
    moyalIntegral (moyalBracket ℏ F G) = 0 := by
  rw [moyalBracket_eq_collisionStar_smul]
  unfold moyalIntegral
  rw [Matrix.trace_smul]
  rw [show (collisionStar F G).trace = moyalIntegral (collisionStar F G) from rfl,
    moyalIntegral_collisionStar, smul_zero]

/-- **[Gayral Theorem 2.2] The Moyal integral is a faithful trace** `∫ f*⋆f = 0 ↔ f = 0`: the
distinguished trace of the Moyal Fréchet algebra separates states — no nonzero element has vanishing
`L²` mass. -/
theorem moyalIntegral_faithful (F : Matrix (Fin d) (Fin d) ℂ) :
    moyalIntegral (Fᴴ * F) = 0 ↔ F = 0 :=
  Matrix.trace_conjTranspose_mul_self_eq_zero_iff

/-- **Reality of the Moyal integral** `∫ f* = conj ∫ f` — complex conjugation of functions (the Moyal
involution) conjugates the integral. -/
theorem moyalIntegral_star (F : Matrix (Fin d) (Fin d) ℂ) :
    moyalIntegral Fᴴ = star (moyalIntegral F) :=
  Matrix.trace_conjTranspose F

/-- **The volume of the truncated Moyal plane** `∫ 1 = d` — each of the `d` oscillator levels carries
exactly one unit of normalized phase-space volume: the finite Weyl law of the matricial truncation. -/
theorem moyalIntegral_one : moyalIntegral (1 : Matrix (Fin d) (Fin d) ℂ) = (d : ℂ) := by
  unfold moyalIntegral
  rw [Matrix.trace_one]
  simp

end Physlib.QuantumMechanics.ComplexAction.Moyal.MoyalTraceIntegral

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Moyal.MoyalTraceIntegral.moyalIntegral_tracial where
  formalizes @ "claim:the-moyal-integral-is-cyclic-under-the-moyal-product-the-tracial-property",
  supported_by @ "paper:gayral-gracia-bondia-iochum-schucker-varilly-moyal-planes-are-spectral-triples"

zil attach Physlib.QuantumMechanics.ComplexAction.Moyal.MoyalTraceIntegral.moyalIntegral_moyalBracket where
  supported_by @ "lean:RelEntropy.faithful",
  supported_by @ "lean:Physlib.QuantumMechanics.ComplexAction.Moyal.BakerOperatorSplit.moyalBracket_eq_collisionStar_smul",
  formalizes @ "claim:the-phase-space-integral-of-a-moyal-bracket-vanishes-so-moyal-evolution-conserves-expectation-values",
  requires @ "claim:the-moyal-integral-is-cyclic-under-the-moyal-product-the-tracial-property"

zil attach Physlib.QuantumMechanics.ComplexAction.Moyal.MoyalTraceIntegral.moyalIntegral_faithful where
  formalizes @ "claim:the-moyal-integral-is-a-faithful-trace-vanishing-l2-mass-forces-the-zero-element",
  supported_by @ "paper:gayral-gracia-bondia-iochum-schucker-varilly-moyal-planes-are-spectral-triples"

zil attach Physlib.QuantumMechanics.ComplexAction.Moyal.MoyalTraceIntegral.moyalIntegral_moyalUnit where
  formalizes @ "claim:only-the-diagonal-gaussian-eigentransitions-carry-phase-space-volume-the-integral-of-f-mn-is-delta-mn"

zil attach Physlib.QuantumMechanics.ComplexAction.Moyal.MoyalTraceIntegral.moyalIntegral_one where
  supported_by @ "lean:HermitianMat.trace_one",
  formalizes @ "claim:each-oscillator-level-carries-one-unit-of-normalized-phase-space-volume-the-finite-weyl-law"

zil_file_contract physlib.moyalTraceIntegral where
  promises "The Moyal integral completed on the matricial model: the normalized phase-space integral is the matrix trace, cyclic under the Moyal product (the tracial property of Gayral Lemma 2.1(v)), faithful (Gayral Theorem 2.2: vanishing L2 mass forces zero), real under the Moyal involution, annihilating the star-commutator and the Hiley Moyal bracket (so Moyal evolution conserves expectation values), assigning delta_mn volume to the eigentransitions and total volume d to the truncated plane (the finite Weyl law)."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.Moyal.MoyalTraceIntegral.moyalIntegral",
    "lean:Physlib.QuantumMechanics.ComplexAction.Moyal.OscillatorMatrixUnits.moyalUnit",
    "lean:Physlib.QuantumMechanics.ComplexAction.Moyal.BakerOperatorSplit.moyalBracket"]
  forbids_substitutes ["the oscillatory Lebesgue integral over R^2N, the integral functional is carried exactly by the matricial trace on the eigentransition truncation"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.Moyal.MoyalTraceIntegral.moyalIntegral_moyalUnit,
    Physlib.QuantumMechanics.ComplexAction.Moyal.MoyalTraceIntegral.moyalIntegral_tracial,
    Physlib.QuantumMechanics.ComplexAction.Moyal.MoyalTraceIntegral.moyalIntegral_collisionStar,
    Physlib.QuantumMechanics.ComplexAction.Moyal.MoyalTraceIntegral.moyalIntegral_moyalBracket,
    Physlib.QuantumMechanics.ComplexAction.Moyal.MoyalTraceIntegral.moyalIntegral_faithful,
    Physlib.QuantumMechanics.ComplexAction.Moyal.MoyalTraceIntegral.moyalIntegral_star,
    Physlib.QuantumMechanics.ComplexAction.Moyal.MoyalTraceIntegral.moyalIntegral_one]

/- ZIL-END -/

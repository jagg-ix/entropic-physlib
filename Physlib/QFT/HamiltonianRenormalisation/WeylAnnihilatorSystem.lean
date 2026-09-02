/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.QFT.HamiltonianRenormalisation.DirectHamiltonianFlow
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Weyl elements, annihilators, and coherent matrix elements
(Hamiltonian renormalisation II, Eqs. 3.113–3.120)

The bosonic operator layer of §3.2 of Lang–Liegener–Thiemann, *Hamiltonian renormalisation II*
(arXiv:1711.06727v2), over an **arbitrary** real inner-product one-particle space — the general
form of the structure that the two-dimensional symplectic module `WeylCCRSpacetime` only
exhibits as a toy.  A `WeylAnnihilatorSystem` bundles the Weyl elements `W(f) = e^{iφ[f]}`, the
Fock vacuum, the smeared annihilators `a(g)` with `a(g)Ω = 0` (Eq. 3.113), and the Weyl-shift
relation (Eq. 3.115)

  `a(g) W(f) = W(f) (a(g) + i·s·⟨g, ω^{−1/2}f⟩·1)`,

the only piece of the canonical commutation relations that the renormalisation computations of
§3.2 consume.  From these axioms the paper's matrix-element chain is derived:

* `ann_coherent` — the annihilator has the coherent vectors `W(f)Ω` as eigenvectors, with
  eigenvalue the c-number shift of Eq. 3.115.
* `hamForm`, `hamForm_coherent` — **Eqs. 3.116–3.117**: the quadratic Hamiltonian form
  `⟨aΨ, ω aΦ⟩` evaluated between coherent vectors factors as
  `s²·⟨ω^{−1/2}f, ω ω^{−1/2}f'⟩·⟨W(f)Ω, W(f')Ω⟩` — the annihilators collapse to their
  eigenvalues and the mode sum contracts by Parseval.
* `hamForm_coherent_normalized` — with `ω^{−1/2}·ω·ω^{−1/2} = 1` the coefficient is exactly
  `s²·⟨f, f'⟩`: the matrix elements of `H = ⟨a, ω a⟩` between coherent vectors display the
  one-particle inner product of the smearing functions.
* `hamForm_coherent_isometric` — **Eqs. 3.112 + 3.117–3.120**: probing the fine Hamiltonian on
  coherent vectors with coarse-grained labels `I·f`, the isometry of `I` gives the *same*
  coefficient `s²·⟨f, f'⟩` at the coarse resolution — the direct Hamiltonian flow preserves the
  form of Eq. 3.116 with unchanged constants at every step, and instantiated with the continuum
  embedding `J` this is the fixed-point Hamiltonian sandwich `H*_M = J† H_R J` on generators.
* `vectorState_flow` — **Eqs. 3.114 + 3.109**: if the vacuum vector state of the system is the
  Gaussian generating functional `gaussianWeyl C`, its pullback along an embedding is the
  Gaussian generating functional with the flowed covariance `I† C I`.

**Honest layering.**  The axioms are consumed, not constructed: `commutativeSystem` shows they
are consistent (the degenerate commutative case with vanishing shift), but a faithful Fock
representation — `L²` of a Gaussian measure or the Bargmann space, where Eq. 3.115 is a theorem
— is future material, as are self-adjointness of the Hamiltonian and the unitarity of the Weyl
elements, which the matrix-element computations above never use.  `hamForm` is written against a
fixed orthonormal mode basis, as in the paper's lattice formulation; basis independence would
need linearity of the smearing map `g ↦ a(g)`, which is likewise not consumed here.

## References

* T. Lang, K. Liegener, T. Thiemann, *Hamiltonian renormalisation II: renormalisation flow of
  1+1 dimensional free scalar fields*, arXiv:1711.06727v2, §3.2 (Eqs. 3.112–3.120) and §3.1.2
  (Eqs. 3.95–3.107).
-/

set_option autoImplicit false

open ContinuousLinearMap

@[expose] public section

namespace Physlib.QFT.HamiltonianRenormalisation

/-- **A Weyl–annihilator system** (Eqs. 3.113, 3.115): Weyl elements and smeared annihilators on
a complex Hilbert space `H`, over a real inner-product one-particle space `E`, with a Fock
vacuum annihilated by every `a(g)` and the Weyl-shift relation
`a(g)W(f) = W(f)(a(g) + i·s·⟨g, ω^{−1/2}f⟩)`.  The operator `halfInv` plays the role of
`ω^{−1/2}` and `scale` the role of `√(ℏκ/2)` in the paper's normalisation. -/
structure WeylAnnihilatorSystem (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] where
  /-- The Weyl element `W(f) = e^{iφ[f]}`. -/
  weyl : E → H →L[ℂ] H
  /-- The Fock vacuum. -/
  vacuum : H
  /-- The smeared annihilator `a(g)`. -/
  ann : E → H →L[ℂ] H
  /-- The scale `√(ℏκ/2)` of Eq. 3.115. -/
  scale : ℝ
  /-- The inverse square root `ω^{−1/2}` of the frequency operator. -/
  halfInv : E →L[ℝ] E
  /-- The vacuum is annihilated, `a(g)Ω = 0` (Eq. 3.113). -/
  ann_vacuum : ∀ g, ann g vacuum = 0
  /-- **Eq. 3.115**: conjugating the annihilator with a Weyl element shifts it by the c-number
  `i·s·⟨g, ω^{−1/2}f⟩`. -/
  ann_weyl : ∀ f g, (ann g) ∘L (weyl f)
    = (weyl f) ∘L (ann g + (Complex.I * (scale : ℂ) * ((inner ℝ g (halfInv f) : ℝ) : ℂ)) • 1)

namespace WeylAnnihilatorSystem

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  (S : WeylAnnihilatorSystem E H)

/-- **Coherent vectors are annihilator eigenvectors**: `a(g) W(f)Ω = i·s·⟨g, ω^{−1/2}f⟩·W(f)Ω`
— Eq. 3.115 applied to the vacuum. -/
theorem ann_coherent (f g : E) :
    S.ann g (S.weyl f S.vacuum)
      = (Complex.I * (S.scale : ℂ) * ((inner ℝ g (S.halfInv f) : ℝ) : ℂ)) • S.weyl f S.vacuum := by
  have h := congrArg (fun T : H →L[ℂ] H => T S.vacuum) (S.ann_weyl f g)
  simp only [comp_apply, add_apply, smul_apply, S.ann_vacuum, zero_add] at h
  rw [h, map_smul]
  rfl

/-- **The quadratic Hamiltonian form** `⟨aΨ, ω aΦ⟩` of Eq. 3.116, written against an
orthonormal mode basis `b`: `Σ_i ⟨a(b i)Ψ, a(ω b i)Φ⟩`. -/
noncomputable def hamForm {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (ω : E →L[ℝ] E) (Ψ Φ : H) : ℂ :=
  ∑ i, inner ℂ (S.ann (b i) Ψ) (S.ann (ω (b i)) Φ)

/-- **Eqs. 3.116–3.117, the coherent matrix elements**: between coherent vectors the quadratic
Hamiltonian form factors — the annihilators collapse to their eigenvalues, and the mode sum
contracts by Parseval to the one-particle pairing `s²·⟨ω^{−1/2}f, ω ω^{−1/2}f'⟩` times the
coherent overlap. -/
theorem hamForm_coherent {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (ω : E →L[ℝ] E) (hω : ∀ x y, inner ℝ (ω x) (y) = inner ℝ (x) (ω y)) (f f' : E) :
    S.hamForm b ω (S.weyl f S.vacuum) (S.weyl f' S.vacuum)
      = ((S.scale^2 * inner ℝ (S.halfInv f) (ω (S.halfInv f')) : ℝ) : ℂ)
          * inner ℂ (S.weyl f S.vacuum) (S.weyl f' S.vacuum) := by
  unfold hamForm
  have key : ∀ i : ι,
      (inner ℂ (S.ann (b i) (S.weyl f S.vacuum)) (S.ann (ω (b i)) (S.weyl f' S.vacuum)))
        = ((S.scale^2 * (inner ℝ (b i) (S.halfInv f) * inner ℝ (ω (b i)) (S.halfInv f')) : ℝ) : ℂ)
            * inner ℂ (S.weyl f S.vacuum) (S.weyl f' S.vacuum) := by
    intro i
    rw [S.ann_coherent f (b i), S.ann_coherent f' (ω (b i)),
      inner_smul_left, inner_smul_right]
    simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    ring
  rw [Finset.sum_congr rfl fun i _ => key i, ← Finset.sum_mul]
  congr 1
  push_cast
  rw [← Finset.mul_sum]
  congr 1
  calc ∑ i, ((inner ℝ (b i) (S.halfInv f) : ℝ) : ℂ) * ((inner ℝ (ω (b i)) (S.halfInv f') : ℝ) : ℂ)
      = ((∑ i, inner ℝ (S.halfInv f) (b i) * inner ℝ (b i) (ω (S.halfInv f')) : ℝ) : ℂ) := by
        push_cast
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hω, real_inner_comm (b i) (S.halfInv f)]
    _ = ((inner ℝ (S.halfInv f) (ω (S.halfInv f')) : ℝ) : ℂ) := by
        rw [b.sum_inner_mul_inner]

/-- **Eq. 3.117, normalized**: with `ω^{−1/2}·ω·ω^{−1/2} = 1` the coefficient is exactly
`s²·⟨f, f'⟩` — the matrix elements of `H = ⟨a, ω a⟩` between coherent vectors display the
one-particle inner product of the smearing functions. -/
theorem hamForm_coherent_normalized {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (ω : E →L[ℝ] E) (hω : ∀ x y, inner ℝ (ω x) (y) = inner ℝ (x) (ω y))
    (hK : ∀ u v : E, inner ℝ (S.halfInv u) (ω (S.halfInv v)) = inner ℝ (u) (v)) (f f' : E) :
    S.hamForm b ω (S.weyl f S.vacuum) (S.weyl f' S.vacuum)
      = ((S.scale^2 * inner ℝ (f) (f') : ℝ) : ℂ)
          * inner ℂ (S.weyl f S.vacuum) (S.weyl f' S.vacuum) := by
  rw [S.hamForm_coherent b ω hω f f', hK]

/-- **The direct Hamiltonian flow preserves the form of Eq. 3.116**
(Eqs. 3.112, 3.117–3.120): probing the fine Hamiltonian on coherent vectors with coarse-grained
labels `I·f`, the isometry of the embedding returns the coefficient `s²·⟨f, f'⟩` in the *coarse*
one-particle inner product — the flowed matrix elements are again those of a quadratic
Hamiltonian with unchanged constants.  Instantiated with the continuum embedding `J` this is the
fixed-point Hamiltonian sandwich `H*_M = J† H_R J` evaluated on generators. -/
theorem hamForm_coherent_isometric {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E)
    (ω : E →L[ℝ] E) (hω : ∀ x y, inner ℝ (ω x) (y) = inner ℝ (x) (ω y))
    (hK : ∀ u v : E, inner ℝ (S.halfInv u) (ω (S.halfInv v)) = inner ℝ (u) (v))
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (I : F →L[ℝ] E) (hI : ∀ u v : F, inner ℝ (I u) (I v) = inner ℝ (u) (v)) (f f' : F) :
    S.hamForm b ω (S.weyl (I f) S.vacuum) (S.weyl (I f') S.vacuum)
      = ((S.scale^2 * inner ℝ (f) (f') : ℝ) : ℂ)
          * inner ℂ (S.weyl (I f) S.vacuum) (S.weyl (I f') S.vacuum) := by
  rw [S.hamForm_coherent_normalized b ω hω hK (I f) (I f'), hI]

/-- **Eqs. 3.114 + 3.109**: if the vacuum vector state of the system is the Gaussian generating
functional with covariance `C`, then its pullback along an embedding `I` — the direct-flow
definition of the coarse measure — is the Gaussian generating functional with the flowed
covariance `I† C I`. -/
theorem vectorState_flow [CompleteSpace E]
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    (C : E →L[ℝ] E) (I : F →L[ℝ] E)
    (hgen : ∀ f : E, (inner ℂ (S.vacuum) (S.weyl f S.vacuum)) = ((gaussianWeyl C f : ℝ) : ℂ))
    (f : F) :
    (inner ℂ (S.vacuum) (S.weyl (I f) S.vacuum))
      = ((gaussianWeyl (adjoint I ∘L (C ∘L I)) f : ℝ) : ℂ) := by
  rw [hgen (I f), gaussianWeyl_flow]

/-- **Consistency of the axioms**: the degenerate commutative system — trivial Weyl elements,
vanishing annihilators and shift — satisfies every field.  A faithful Fock representation, where
the shift relation Eq. 3.115 is a theorem rather than an axiom, is future material. -/
noncomputable def commutativeSystem (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] : WeylAnnihilatorSystem E ℂ where
  weyl _ := 1
  vacuum := 1
  ann _ := 0
  scale := 0
  halfInv := 0
  ann_vacuum _ := rfl
  ann_weyl f g := by
    simp

end WeylAnnihilatorSystem

end Physlib.QFT.HamiltonianRenormalisation

end

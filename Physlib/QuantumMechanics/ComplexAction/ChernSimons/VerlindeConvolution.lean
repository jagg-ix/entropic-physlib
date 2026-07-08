/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.VerlindeFormula
public import Physlib.QuantumMechanics.ComplexAction.ChernSimons.WilsonLoopBraidingRibbon

/-!
# The Verlinde `S`-matrix diagonalizes the fusion convolution (the discrete convolution theorem)

This file makes precise the single statement underlying the link between **Yang–Baxter convolution algebras**,
**Verlinde fusion**, and the **braiding** of `U(1)_k` Chern–Simons: the Verlinde `S`-matrix is the discrete
Fourier / Gauss-sum transform, and *Fourier diagonalizes convolution*.

The fusion ring of `U(1)_k` is the group algebra of the charge lattice `ℤ/k`; its product is the **cyclic
convolution** `(f ⋆ g)(c) = Σ_a f(a) g(c−a)` (`cswConvolution`) — the same convolution structure in which the
Yang–Baxter relation lives (`OperatorAlgebra.YangBaxterConvolutionAlgebra`, `convolution_yangBaxter_iff`). The Verlinde
`S`-matrix `S_{ab} = (1/√k) e^{−2πi ab/k}` defines the transform `cswDFT f (x) = Σ_a S_{ax} f(a)`.

* **The character / group-like property** (`cswSMatrix_add_left`): `S_{(a+b)x} = √k · S_{ax} · S_{bx}` — the
  `S`-matrix columns are characters of `ℤ/k`. The same property on the braiding phase
  `B_{ab} = e^{2πi ab/k} = √k · conj(S_{ab})` (`ChernSimons.WilsonLoopBraidingRibbon.wilsonBraidingPhase`) is
  `wilsonBraidingPhase_add_left`: `B_{(a+b)x} = B_{ax} · B_{bx}`, i.e. the braiding is a *bicharacter* — the
  shared kernel of the Yang–Baxter/braiding side and the Verlinde side.
* **The convolution theorem** (`cswDFT_convolution`): `Ŝ(f ⋆ g) = √k · Ŝ(f) · Ŝ(g)`. The transform turns the
  fusion convolution into pointwise multiplication — i.e. the Verlinde `S`-matrix **diagonalizes the fusion
  algebra**, which is the content of the Verlinde formula (`cswVerlinde_formula`) read as "Fourier
  diagonalizes convolution".
* **Convolution of charges = fusion** (`cswConvolution_single`): `δ_a ⋆ δ_b = δ_{a+b}` — convolution of point
  charges is charge addition, the abelian fusion rule.

In the continuum / path-integral picture the same `S` is the modular `S` transform of the theta function
(Poisson summation, `cswTheta_modular_S`), and the convergent contour for the oscillatory weight `e^{iS}` is
the entropically damped one `‖e^{iS/ℏ}‖ = e^{−S_I/ℏ}` (`RigorousComplexFK`); this file is the finite,
fully-proved shadow of that duality.

## References

* E. Verlinde (1988); E. Witten (1989). Gorbounov–Korff–Stroppel, *Yang–Baxter algebras as convolution
  algebras* (arXiv:1802.09497). `Physlib` (`cswSMatrix`, `cswDFT_orthogonality`, `cswVerlinde_formula`,
  `wilsonBraidingPhase`).

No additional assumptions.
-/

set_option autoImplicit false

open Complex
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.Gravity
open Physlib.QuantumMechanics.ComplexAction.ChernSimons.WilsonLoopBraidingRibbon

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ChernSimons.VerlindeConvolution

variable {k : ℕ}

/-- **The cyclic (fusion) convolution** on functions of the `U(1)_k` charge lattice `ℤ/k`:
`(f ⋆ g)(c) = Σ_a f(a) g(c − a)` — the product of the abelian fusion ring. -/
noncomputable def cswConvolution (f g : Fin k → ℂ) : Fin k → ℂ :=
  fun c => ∑ a : Fin k, f a * g (c - a)

/-- **The Verlinde / discrete-Fourier transform** `Ŝf (x) = Σ_a S_{ax} f(a)`. -/
noncomputable def cswDFT (f : Fin k → ℂ) : Fin k → ℂ :=
  fun x => ∑ a : Fin k, cswSMatrix k a x * f a

/-! ## §A — the shared character kernel -/

/-- **[Charge periodicity of the exponential kernel]** the `ℤ/k` exponential `e^{c·2πi·(·)·x/k}` only sees the
charge mod `k`: `e^{c·2πi·(a+b).val·x/k} = e^{c·2πi·(a.val+b.val)·x/k}` for any integer weight `c`. -/
theorem exp_charge_period (hk : 0 < k) (a b x : Fin k) (c : ℤ) :
    Complex.exp ((c : ℂ) * (2 * (Real.pi : ℂ) * I) * ((a + b).val : ℂ) * (x.val : ℂ) / (k : ℂ))
      = Complex.exp ((c : ℂ) * (2 * (Real.pi : ℂ) * I)
          * ((a.val : ℂ) + (b.val : ℂ)) * (x.val : ℂ) / (k : ℂ)) := by
  haveI : NeZero k := ⟨hk.ne'⟩
  have hk0 : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  have hdm := Nat.div_add_mod (a.val + b.val) k
  set m : ℕ := (a.val + b.val) / k with hm
  have hle : k * m ≤ a.val + b.val := by omega
  have hval : ((a + b).val : ℂ) = (a.val : ℂ) + (b.val : ℂ) - (k : ℂ) * (m : ℂ) := by
    have h1 : (a + b).val = a.val + b.val - k * m := by rw [Fin.val_add]; omega
    rw [h1, Nat.cast_sub hle]; push_cast; ring
  rw [hval,
    show (c : ℂ) * (2 * (Real.pi : ℂ) * I) * ((a.val : ℂ) + (b.val : ℂ) - (k : ℂ) * (m : ℂ))
          * (x.val : ℂ) / (k : ℂ)
        = (c : ℂ) * (2 * (Real.pi : ℂ) * I) * ((a.val : ℂ) + (b.val : ℂ)) * (x.val : ℂ) / (k : ℂ)
          + ((-(c * (x.val : ℤ) * (m : ℤ)) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I) from by
      push_cast; field_simp; ring,
    Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **[The `S`-matrix columns are characters]** `S_{(a+b)x} = √k · S_{ax} · S_{bx}`: the Verlinde `S`-matrix
kernel is multiplicative in the charge (up to the `√k` normalization) — the group-like / Hopf-character
property of `ℤ/k`. -/
theorem cswSMatrix_add_left (hk : 0 < k) (a b x : Fin k) :
    cswSMatrix k (a + b) x = (Real.sqrt k : ℂ) * cswSMatrix k a x * cswSMatrix k b x := by
  have hsk : (Real.sqrt k : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hk)).ne'
  unfold cswSMatrix
  rw [show -(2 * (Real.pi : ℂ) * I * ((a + b).val : ℂ) * (x.val : ℂ)) / (k : ℂ)
        = ((-1 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I) * ((a + b).val : ℂ) * (x.val : ℂ) / (k : ℂ) from by
      push_cast; ring,
    exp_charge_period hk a b x (-1),
    show ((-1 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I) * ((a.val : ℂ) + (b.val : ℂ)) * (x.val : ℂ) / (k : ℂ)
        = -(2 * (Real.pi : ℂ) * I * (a.val : ℂ) * (x.val : ℂ)) / (k : ℂ)
          + -(2 * (Real.pi : ℂ) * I * (b.val : ℂ) * (x.val : ℂ)) / (k : ℂ) from by
      push_cast; field_simp; ring,
    Complex.exp_add]
  field_simp

/-- **[The braiding phase is a bicharacter]** `B_{(a+b)x} = B_{ax} · B_{bx}` for the Wilson-line braiding
phase `B_{ab} = e^{2πi ab/k}`: the Yang–Baxter / braiding kernel is multiplicative in the charge — the same
character that the Verlinde `S`-matrix (`cswSMatrix_add_left`) records, since `B = √k · conj S`
(`wilsonBraidingPhase_eq_S`). -/
theorem wilsonBraidingPhase_add_left (hk : 0 < k) (a b x : Fin k) :
    wilsonBraidingPhase k (a + b) x = wilsonBraidingPhase k a x * wilsonBraidingPhase k b x := by
  unfold wilsonBraidingPhase
  rw [show 2 * (Real.pi : ℂ) * I * ((a + b).val : ℂ) * (x.val : ℂ) / (k : ℂ)
        = ((1 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I) * ((a + b).val : ℂ) * (x.val : ℂ) / (k : ℂ) from by
      push_cast; ring,
    exp_charge_period hk a b x 1,
    show ((1 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I) * ((a.val : ℂ) + (b.val : ℂ)) * (x.val : ℂ) / (k : ℂ)
        = 2 * (Real.pi : ℂ) * I * (a.val : ℂ) * (x.val : ℂ) / (k : ℂ)
          + 2 * (Real.pi : ℂ) * I * (b.val : ℂ) * (x.val : ℂ) / (k : ℂ) from by
      push_cast; ring,
    Complex.exp_add]

/-! ## §B — the convolution theorem -/

/-- **[The discrete convolution theorem — Verlinde `S` diagonalizes fusion]** `Ŝ(f ⋆ g) = √k · Ŝf · Ŝg`: the
Verlinde / Gauss-sum transform turns the fusion convolution into pointwise multiplication. This is the
diagonalization of the `U(1)_k` fusion algebra by the `S`-matrix — the structural content of the Verlinde
formula. -/
theorem cswDFT_convolution (hk : 0 < k) (f g : Fin k → ℂ) (x : Fin k) :
    cswDFT (cswConvolution f g) x = (Real.sqrt k : ℂ) * cswDFT f x * cswDFT g x := by
  haveI : NeZero k := ⟨hk.ne'⟩
  simp only [cswDFT, cswConvolution]
  calc ∑ c : Fin k, cswSMatrix k c x * ∑ a : Fin k, f a * g (c - a)
      = ∑ c : Fin k, ∑ a : Fin k, cswSMatrix k c x * (f a * g (c - a)) := by
        exact Finset.sum_congr rfl fun c _ => Finset.mul_sum _ _ _
    _ = ∑ a : Fin k, ∑ c : Fin k, cswSMatrix k c x * (f a * g (c - a)) := Finset.sum_comm
    _ = ∑ a : Fin k, ∑ b : Fin k, cswSMatrix k (a + b) x * (f a * g b) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Equiv.sum_comp (Equiv.addLeft a) fun c => cswSMatrix k c x * (f a * g (c - a))]
        refine Finset.sum_congr rfl fun b _ => ?_
        show cswSMatrix k (a + b) x * (f a * g (a + b - a)) = cswSMatrix k (a + b) x * (f a * g b)
        rw [add_sub_cancel_left]
    _ = ∑ a : Fin k, ∑ b : Fin k,
          (Real.sqrt k : ℂ) * (cswSMatrix k a x * f a) * (cswSMatrix k b x * g b) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [cswSMatrix_add_left hk a b x]; ring
    _ = (Real.sqrt k : ℂ) * cswDFT f x * cswDFT g x := by
        simp only [cswDFT]
        conv_rhs => rw [mul_assoc, Finset.sum_mul_sum]
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun b _ => by ring

/-- **[Convolution of point charges = fusion]** `δ_a ⋆ δ_b = δ_{a+b}`: convolving the indicator of charge `a`
with that of charge `b` gives the indicator of `a + b` — the abelian `U(1)_k` fusion rule `a × b = a+b`. -/
theorem cswConvolution_single (hk : 0 < k) (a b : Fin k) :
    cswConvolution (Pi.single a 1) (Pi.single b (1 : ℂ)) = Pi.single (a + b) 1 := by
  haveI : NeZero k := ⟨hk.ne'⟩
  funext c
  simp only [cswConvolution]
  rw [Finset.sum_eq_single a]
  · rw [Pi.single_eq_same, one_mul, Pi.single_apply, Pi.single_apply]
    exact if_congr (by rw [sub_eq_iff_eq_add, add_comm b a]) rfl rfl
  · intro a' _ ha'; rw [Pi.single_eq_of_ne ha', zero_mul]
  · intro h; exact absurd (Finset.mem_univ a) h

end Physlib.QuantumMechanics.ComplexAction.ChernSimons.VerlindeConvolution

end

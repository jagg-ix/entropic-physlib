/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Data.Matrix.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# The Moyal bracket and the static Toda lattice

Ports the two exact, self-contained integrable-systems cores of the catept-main publication bridge
(`NCTodaMoyalBridge`) — the noncommutative Moyal-plane bracket and the Toda lattice — into physlib (the QTM
deformation-parameter section, which depends on catept carriers, is excluded). Neither was present in physlib.

**§A — the Moyal bracket.** On a truncated finite-mode field `MoyalField K = Fin K → ℂ`, the leading-order
(first order in the deformation `θ`) antisymmetric piece of the Moyal star-commutator `f ⋆ g − g ⋆ f` is

  `[f, g]_⋆(i,j) = θ·(fᵢ gⱼ − fⱼ gᵢ)`   (`moyalBracket`),

a `K×K` matrix. It is **antisymmetric** (`moyalBracket_antisymm`), vanishes on the diagonal-pairing
(`moyalBracket_self`), vanishes in the **commutative limit** `θ = 0` (`moyalBracket_zero_theta`), and is
`ℝ`-bilinear in `θ` and in the fields (`moyalBracket_add_theta`, `moyalBracket_add_left`).

**§B — the static Toda lattice.** For a configuration `f : ℤ → ℝ` independent of the light-cone coordinates,
the Toda lattice equation `∂₊∂₋ qₙ = e^{q_{n+1}−qₙ} − e^{qₙ−q_{n−1}}` has vanishing left side, so its solutions
are the zeros of the residual

  `R(f,n) = e^{f(n+1)−f(n)} − e^{f(n)−f(n−1)}`   (`todaResidual`).

The exact characterization (`todaResidual_eq_zero_iff`, strengthening the bridge): by injectivity of `exp`,

  `R(f,n) = 0 ⟺ f(n+1) − f(n) = f(n) − f(n−1)`,

i.e. the static Toda solutions are exactly the configurations with **vanishing second difference** — locally
**arithmetic** (the slope `a` is constant). In particular linear configurations `f(n) = a·n + b`
(`todaResidual_linear`) and constants (`todaResidual_const`) solve it.

* **§A — the Moyal bracket** (`MoyalField`, `moyalBracket`, antisymmetry/bilinearity).
* **§B — the static Toda lattice** (`todaResidual`, `todaResidual_eq_zero_iff`, `todaResidual_linear`,
  `todaResidual_const`).

## References

* J. Moyal (the deformation bracket); M. Toda (the exponential lattice). Carrier: `Mathlib` (`Matrix`,
  `Real.exp`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Moyal.BracketTodaLattice


/-- **A truncated finite-mode field on the Moyal plane** `Fin K → ℂ`. -/
abbrev MoyalField (K : ℕ) : Type := Fin K → ℂ

/-- **The truncated Moyal bracket** `[f, g]_⋆(i,j) = θ·(fᵢ gⱼ − fⱼ gᵢ)` — the leading-order antisymmetric piece
of the Moyal star-commutator `f ⋆ g − g ⋆ f`. -/
def moyalBracket {K : ℕ} (θ : ℝ) (f g : MoyalField K) : Matrix (Fin K) (Fin K) ℂ :=
  fun i j => (θ : ℂ) * (f i * g j - f j * g i)

/-- **[Antisymmetry] `[g, f]_⋆ = −[f, g]_⋆`.** -/
lemma moyalBracket_antisymm {K : ℕ} (θ : ℝ) (f g : MoyalField K) :
    moyalBracket θ g f = -moyalBracket θ f g := by
  funext i j; simp only [moyalBracket, Matrix.neg_apply]; ring

/-- **[Self-pairing vanishes] `[f, f]_⋆ = 0`.** -/
lemma moyalBracket_self {K : ℕ} (θ : ℝ) (f : MoyalField K) : moyalBracket θ f f = 0 := by
  funext i j; simp only [moyalBracket, Matrix.zero_apply]; ring

/-- **[Commutative limit] `θ = 0 ⇒ [f, g]_⋆ = 0`.** -/
lemma moyalBracket_zero_theta {K : ℕ} (f g : MoyalField K) : moyalBracket 0 f g = 0 := by
  funext i j; simp [moyalBracket]

/-- **[`ℝ`-linearity in `θ`].** -/
lemma moyalBracket_add_theta {K : ℕ} (θ₁ θ₂ : ℝ) (f g : MoyalField K) :
    moyalBracket (θ₁ + θ₂) f g = moyalBracket θ₁ f g + moyalBracket θ₂ f g := by
  funext i j; simp only [moyalBracket, Matrix.add_apply]; push_cast; ring

/-- **[Bilinearity in the field] `[f₁ + f₂, g]_⋆ = [f₁, g]_⋆ + [f₂, g]_⋆`.** -/
lemma moyalBracket_add_left {K : ℕ} (θ : ℝ) (f₁ f₂ g : MoyalField K) :
    moyalBracket θ (f₁ + f₂) g = moyalBracket θ f₁ g + moyalBracket θ f₂ g := by
  funext i j; simp only [moyalBracket, Pi.add_apply, Matrix.add_apply]; ring


/-- **The static Toda lattice residual** `R(f,n) = e^{f(n+1)−f(n)} − e^{f(n)−f(n−1)}` — the right side of the
Toda equation `∂₊∂₋ qₙ = e^{q_{n+1}−qₙ} − e^{qₙ−q_{n−1}}` for a light-cone-independent configuration. -/
noncomputable def todaResidual (f : ℤ → ℝ) (n : ℤ) : ℝ :=
  Real.exp (f (n + 1) - f n) - Real.exp (f n - f (n - 1))

/-- **[Static Toda solution ⟺ vanishing second difference] `R(f,n) = 0 ⟺ f(n+1) − f(n) = f(n) − f(n−1)`.** By
injectivity of `exp`, a configuration solves the static Toda lattice at `n` exactly when its second
difference vanishes there — locally arithmetic (constant slope). -/
lemma todaResidual_eq_zero_iff (f : ℤ → ℝ) (n : ℤ) :
    todaResidual f n = 0 ↔ f (n + 1) - f n = f n - f (n - 1) := by
  rw [todaResidual, sub_eq_zero, Real.exp_eq_exp]

/-- **[Linear configurations solve the static Toda lattice]** `f(n) = a·n + b ⇒ R(f,n) = 0`. -/
lemma todaResidual_linear (a b : ℝ) (n : ℤ) :
    todaResidual (fun k => a * (k : ℝ) + b) n = 0 :=
  (todaResidual_eq_zero_iff _ n).2 (by push_cast; ring)

/-- **[Constant configurations solve the static Toda lattice]** (the slope-`0` base case). -/
lemma todaResidual_const (c : ℝ) (n : ℤ) : todaResidual (fun _ => c) n = 0 :=
  (todaResidual_eq_zero_iff _ n).2 (by ring)

end Physlib.QuantumMechanics.ComplexAction.Moyal.BracketTodaLattice

end

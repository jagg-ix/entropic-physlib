/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
/- ZIL-BEGIN -/
public meta import Zil
/- ZIL-END -/

/-!
# Padmanabhan's conjugate variables and the well-posed gravitational action (Chakraborty)

Formalizes the algebraic core of S. Chakraborty, *Boundary terms of the Einstein–Hilbert action*
(arXiv:1607.05986), §2: the Einstein–Hilbert action is not well posed in the metric `g_{ab}` because its
Ricci-scalar Lagrangian carries second derivatives that force fixing both `g` and `∂g` on the boundary
(the origin of the Gibbons–Hawking–York term, `GHYSurfaceTerm`). Padmanabhan's resolution promotes the
connection to a new variable

  `N^a_{bc} = Q^{ad}_{ce} Γ^e_{bd} + Q^{ad}_{be} Γ^e_{cd}`,   `Q^{ab}_{cd} = ½(δ^a_c δ^b_d − δ^a_d δ^b_c)`
  (Eq 1),

paired with `f^{ab} = √(−g) g^{ab}`, giving a well-posed variational principle. The paper's key structural
point is that the **inverse** relation reconstructing `Γ` from `N` is *dimension dependent* (Eq 2),

  `Γ^c_{ab} = −N^c_{ab} + (1/(D−1))(N^d_{ad} δ^c_b + N^d_{bd} δ^c_a)`,

and the `1/(D−1)` originates from the trace of the `Q`-antisymmetrizer,
`Σ_a Q^{ab}_{ad} = ½(D−1) δ^b_d` (`Qtensor_trace`). Here `D = Fintype.card ι` is the spacetime dimension.

Everything is carried at the exact index-algebra level over an index type `ι`:

* **§A — the `Q`-antisymmetrizer (any index type).** `Qtensor`, `Qtensor_antisymm_upper` /
  `Qtensor_antisymm_lower` (antisymmetry in each index pair). These need only `[DecidableEq ι]` and hold
  for an *arbitrary* — in particular infinite — index type.
* **§B — the trace relations (finite index).** `connectionTrace` (`Γ^d_{bd}`), `NfromGamma` (Eq 1 in the
  equivalent trace form), `Qtensor_trace` (`Σ_a Q^{ab}_{ad} = ½(D−1) δ^b_d` — the origin of the
  `1/(D−1)`), `momentumTrace` (`N^d_{ad}`), `momentumTrace_NfromGamma` (`N^d_{ad} = ½(D−1) Γ^d_{ad}`).
* **§C — the exact inversion.** `gammaFromN` (Eq 2), `gammaFromN_NfromGamma`
  (`Γ` is exactly recovered from `N` in any dimension `D ≥ 2`) — the well-posedness statement.
* **§D — the finite-dimensional obstruction to infinite index.** The trace reconstruction is intrinsically
  finite: `Σ_a δ^a_a = D` and the coefficient `1/(D−1)` both require `D = card ι < ∞`. It degenerates at
  the boundary of validity — `momentumTrace_NfromGamma_card_one` shows the momentum trace vanishes
  identically at `D = 1`, the same degeneracy that sends `1/(D−1) → 0` as `D → ∞`. So the connection
  cannot be recovered from `N` in infinite dimensions: the `(f^{ab}, N^a_{bc})` variables are a genuinely
  finite-dimensional reformulation, even though the antisymmetrizer algebra (§A) is dimension-free.

## References

* S. Chakraborty, *Boundary terms of the Einstein–Hilbert action*, Fundam. Theor. Phys. 187 (2017) 43,
  arXiv:1607.05986 — §2, Eqs (1)–(2); T. Padmanabhan, the `(f^{ab}, N^a_{bc})` variables. Companion to
  `GHYSurfaceTerm` (the boundary term this well-posed reformulation removes the need for).
-/

set_option autoImplicit false

open Finset

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.GravitationalActionConjugateVariables

variable {ι : Type*} [DecidableEq ι]

/-- The Kronecker delta `δ^a_b`. -/
def kron (a b : ι) : ℝ := if a = b then 1 else 0

@[simp] lemma kron_self (a : ι) : kron a a = 1 := by simp [kron]

/-! ### §A — the `Q`-antisymmetrizer (any index type) -/

/-- Padmanabhan's antisymmetrizer `Q^{ab}_{cd} = ½(δ^a_c δ^b_d − δ^a_d δ^b_c)` (Chakraborty Eq 1),
independent of spacetime dimension — defined for an arbitrary (possibly infinite) index type `ι`. -/
noncomputable def Qtensor (a b c d : ι) : ℝ := (kron a c * kron b d - kron a d * kron b c) / 2

/-- **[Antisymmetry in the upper pair]** `Q^{ab}_{cd} = −Q^{ba}_{cd}` (any index type). -/
lemma Qtensor_antisymm_upper (a b c d : ι) : Qtensor a b c d = -Qtensor b a c d := by
  unfold Qtensor; ring

/-- **[Antisymmetry in the lower pair]** `Q^{ab}_{cd} = −Q^{ab}_{dc}` (any index type). -/
lemma Qtensor_antisymm_lower (a b c d : ι) : Qtensor a b c d = -Qtensor a b d c := by
  unfold Qtensor; ring

/-! ### §B — the trace relations (finite index) -/

section Finite
variable [Fintype ι]

lemma sum_kron_diag : ∑ a : ι, kron a a = (Fintype.card ι : ℝ) := by
  simp [kron, Finset.card_univ]

/-- `∑_d f d · δ^d_a = f a`. -/
lemma sum_mul_kron (f : ι → ℝ) (a : ι) : ∑ d : ι, f d * kron d a = f a := by
  simp only [kron, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

/-- `∑_a δ^a_d · δ^b_a = δ^b_d`. -/
lemma sum_kron_mul_kron (b d : ι) : ∑ a : ι, kron a d * kron b a = kron b d := by
  rw [Finset.sum_eq_single d]
  · rw [kron_self, one_mul]
  · intro a _ hne; simp [kron, hne]
  · intro h; exact absurd (Finset.mem_univ d) h

/-- **[The `Q`-trace is dimension dependent]** `Σ_a Q^{ab}_{ad} = ½(D−1) δ^b_d` — the trace that seeds the
`1/(D−1)` of the inverse relation (Chakraborty Eq 2). -/
lemma Qtensor_trace (b d : ι) :
    ∑ a : ι, Qtensor a b a d = ((Fintype.card ι : ℝ) - 1) / 2 * kron b d := by
  have h1 : ∑ a : ι, Qtensor a b a d
      = ((∑ a : ι, kron a a) * kron b d - ∑ a : ι, kron a d * kron b a) / 2 := by
    unfold Qtensor
    rw [← Finset.sum_div, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [h1, sum_kron_diag, sum_kron_mul_kron]
  ring

/-- The trace of the connection `Γ^d_{bd}` (summed over the repeated index). -/
def connectionTrace (Γ : ι → ι → ι → ℝ) (b : ι) : ℝ := ∑ d : ι, Γ d b d

/-- Padmanabhan's conjugate momentum `N^a_{bc}` in its equivalent trace form (Chakraborty Eq 1
contracted): `N^a_{bc} = −Γ^a_{bc} + ½(Γ^d_{bd} δ^a_c + Γ^d_{cd} δ^a_b)`. -/
noncomputable def NfromGamma (Γ : ι → ι → ι → ℝ) (a b c : ι) : ℝ :=
  -Γ a b c + (connectionTrace Γ b * kron a c + connectionTrace Γ c * kron a b) / 2

/-- The trace of the conjugate momentum `N^d_{ad}`. -/
def momentumTrace (N : ι → ι → ι → ℝ) (a : ι) : ℝ := ∑ d : ι, N d a d

/-- **[The momentum trace is `½(D−1)` the connection trace]** `N^d_{ad} = ½(D−1) Γ^d_{ad}` — the same
`½(D−1)` factor as the `Q`-trace, and the source of the `1/(D−1)` in the inversion. -/
lemma momentumTrace_NfromGamma (Γ : ι → ι → ι → ℝ) (a : ι) :
    momentumTrace (NfromGamma Γ) a
      = ((Fintype.card ι : ℝ) - 1) / 2 * connectionTrace Γ a := by
  have hterm : ∀ d : ι, NfromGamma Γ d a d
      = connectionTrace Γ a / 2 * kron d d + connectionTrace Γ d / 2 * kron d a - Γ d a d := by
    intro d; unfold NfromGamma; ring
  unfold momentumTrace
  rw [Finset.sum_congr rfl (fun d _ => hterm d), Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, sum_kron_diag, sum_mul_kron]
  rw [show (∑ d : ι, Γ d a d) = connectionTrace Γ a from rfl]
  ring

/-! ### §C — the exact inversion -/

/-- The reconstruction of the connection from the conjugate momentum (Chakraborty Eq 2),
`Γ^c_{ab} = −N^c_{ab} + (1/(D−1))(N^d_{ad} δ^c_b + N^d_{bd} δ^c_a)`. -/
noncomputable def gammaFromN (N : ι → ι → ι → ℝ) (c a b : ι) : ℝ :=
  -N c a b + (momentumTrace N a * kron c b + momentumTrace N b * kron c a)
    / ((Fintype.card ι : ℝ) - 1)

/-- **[Well-posedness: `Γ` is exactly recovered from `N`]** in any dimension `D ≥ 2` the inversion Eq 2
returns the original connection, `gammaFromN (NfromGamma Γ) = Γ`. This is the statement that
`(f^{ab}, N^a_{bc})` are genuine conjugate variables — the connection is not lost, so the boundary value
problem is well posed. -/
lemma gammaFromN_NfromGamma (Γ : ι → ι → ι → ℝ) (hD : 2 ≤ Fintype.card ι) (c a b : ι) :
    gammaFromN (NfromGamma Γ) c a b = Γ c a b := by
  have hne : (Fintype.card ι : ℝ) - 1 ≠ 0 := by
    have : (2 : ℝ) ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hD
    linarith
  unfold gammaFromN
  rw [momentumTrace_NfromGamma Γ a, momentumTrace_NfromGamma Γ b]
  unfold NfromGamma
  field_simp
  ring

/-! ### §D — the finite-dimensional obstruction to infinite index -/

/-- **[The reconstruction degenerates at `D = 1`]** when `card ι = 1` the momentum trace vanishes
identically, `N^d_{ad} = 0`, independently of `Γ` — the connection trace is lost and the inversion
coefficient `1/(D−1)` is singular. This is the finite-dimensional obstruction that also sends
`1/(D−1) → 0` as `D → ∞`: the trace-based reconstruction is non-degenerate only for `2 ≤ D < ∞`, whereas
the antisymmetrizer algebra of §A is dimension-free (any, including infinite, `ι`). -/
lemma momentumTrace_NfromGamma_card_one (Γ : ι → ι → ι → ℝ) (hD : Fintype.card ι = 1) (a : ι) :
    momentumTrace (NfromGamma Γ) a = 0 := by
  rw [momentumTrace_NfromGamma, hD]; simp

end Finite

/- ZIL-BEGIN -/

zil attach Qtensor_antisymm_upper where
  formalizes @ "claim:padmanabhan-q-antisymmetrizer-is-antisymmetric-in-its-upper-index-pair",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:index-algebra-of-the-q-tensor-holds-for-any-index-type-not-tied-to-four-dimensional-spacetime"

zil attach Qtensor_trace where
  formalizes @ "claim:trace-of-the-padmanabhan-q-antisymmetrizer-is-half-d-minus-one-delta-the-origin-of-the-inverse-relations-one-over-d-minus-one",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:chakraborty-2017-boundary-terms-einstein-hilbert-action",
  caveat @ "claim:the-dimension-d-is-the-cardinality-of-a-finite-index-type-a-toy-stand-in-for-the-spacetime-dimension"

zil attach momentumTrace_NfromGamma where
  formalizes @ "claim:padmanabhan-momentum-trace-equals-half-d-minus-one-times-the-connection-trace",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:contracted-trace-identity-not-the-full-tensorial-eq-1-of-chakraborty"

zil attach gammaFromN_NfromGamma where
  formalizes @ "claim:padmanabhan-conjugate-variables-are-invertible-connection-recovered-from-momentum-for-dimension-at-least-two-well-posedness",
  epistemic_status @ "consistency-identity",
  supported_by @ "paper:chakraborty-2017-boundary-terms-einstein-hilbert-action",
  requires @ "claim:padmanabhan-momentum-trace-equals-half-d-minus-one-times-the-connection-trace",
  caveat @ "claim:exact-inversion-of-the-scalar-index-algebra-not-a-full-variational-well-posedness-proof-of-the-einstein-hilbert-action"

zil attach momentumTrace_NfromGamma_card_one where
  supported_by @ "lean:momentumTrace_NfromGamma",
  formalizes @ "claim:momentum-trace-vanishes-identically-in-dimension-one-the-finite-dimensional-obstruction-to-inversion",
  epistemic_status @ "consistency-identity",
  caveat @ "claim:degeneracy-at-d-equals-one-illustrates-why-the-one-over-d-minus-one-coefficient-and-hence-the-reconstruction-is-intrinsically-finite-dimensional"

zil_file_contract physlib.gravitationalActionConjugateVariables where
  promises "The algebraic core of Padmanabhan's conjugate variables for the well-posed Einstein-Hilbert action (Chakraborty). The Q-antisymmetrizer Q^{ab}_{cd} = ½(δ^a_c δ^b_d − δ^a_d δ^b_c) and its antisymmetries hold for an arbitrary (in particular infinite) index type (Qtensor_antisymm_upper/lower). The trace relations require a finite index of cardinality D: Σ_a Q^{ab}_{ad} = ½(D−1)δ^b_d (Qtensor_trace) seeds the 1/(D−1) of the inverse relation, and the conjugate momentum inverts exactly to recover the connection for D ≥ 2 (gammaFromN_NfromGamma). The finite-dimensional obstruction is made concrete: at D = 1 the momentum trace vanishes identically (momentumTrace_NfromGamma_card_one), the same degeneracy that sends 1/(D−1) → 0 as D → ∞."
  at_level structural
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.GravitationalActionConjugateVariables.Qtensor",
    "lean:Physlib.QuantumMechanics.ComplexAction.GravitationalActionConjugateVariables.NfromGamma",
    "lean:Physlib.QuantumMechanics.ComplexAction.GravitationalActionConjugateVariables.gammaFromN"]
  forbids_substitutes ["claiming a full variational well-posedness proof of the Einstein-Hilbert action -- only the exact conjugate-variable index algebra and its inversion are formalized",
    "treating the finite index cardinality D as anything more than a toy stand-in for the spacetime dimension"]
  witnessed_by [Qtensor_antisymm_upper, Qtensor_antisymm_lower, Qtensor_trace,
    momentumTrace_NfromGamma, gammaFromN_NfromGamma, momentumTrace_NfromGamma_card_one]

/- ZIL-END -/

end Physlib.QuantumMechanics.ComplexAction.GravitationalActionConjugateVariables

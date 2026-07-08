/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.QuantumSymmetry

/-!
# Greaves–Thomas §2.3: classical spacetime symmetries — the geometric action

Formalizes §2.3 of *H. Greaves, T. Thomas, "The CPT Theorem"* (arXiv:1204.4674): the **geometric action**
that turns a pair of representations into a symmetry of fields. A field theory is a set `D ⊆ K` of
dynamically allowed fields `Φ : M → V`; a symmetry is a transformation of `K` leaving `D` invariant. The
*spacetime* symmetries are those whose action `u` on fields comes from a representation `ω` of `G` on
spacetime `M` and a representation `ρ` of `G` on the value space `V` (Eq. 7):

  `u(g)Φ = ρ(g) ∘ Φ ∘ ω(g⁻¹)`.

Here `ρ` is the `V`-action and `ω` the `M`-action, both modelled as `MulAction G _`, so
`u(g)Φ = fun x ↦ g • Φ (g⁻¹ • x)` (`geometricAction`). The companion `PT`/`CPT` files are exactly this at
`g = ` total inversion: `ω(−1) = −I` (total spacetime inversion) with `ρ(−1) = −iγ⁵` (spinor) or `(−1)^r`
(tensor) — `PTSymmetricQFT.CPTDiracDynamics`, `PTSymmetricQFT.PTTensorDynamics`.

* **§A — the geometric action is a `G`-action** (`geometricAction`, `geometricAction_one`,
  `geometricAction_mul`, `geometricAction_leftInv`). `u(1) = id`, `u(gh) = u(g) ∘ u(h)`: the assignment
  `g ↦ u(g)` is a representation of `G` on the fields `K = M → V`.
* **§B — symmetries form a subgroup** (`IsSymmetry`, `symmetrySubgroup`, `mem_symmetrySubgroup`,
  `gInvariant_iff_symmetrySubgroup_top`). `g` is a symmetry of `D` iff `u(g)` leaves `D` invariant
  (`u(g) '' D = D`); these `g` form a `Subgroup G` — the symmetry group of the theory. `D` is `G`-invariant
  iff that subgroup is all of `G`.
* **§C — internal vs spacetime symmetries** (`geometricAction_internal`). When the spacetime action `ω` is
  trivial, `u(g)Φ = ρ(g) ∘ Φ` is a global **internal** symmetry (a pointwise `V`-rotation); a genuine
  spacetime symmetry has `ω` non-trivial (e.g. `G ≤ ` Lorentz group acting on `M`). This is the footnote
  remark that internal symmetries are the `ω = 1` geometric actions.

On the formula side, a geometric action on `K` dualizes to an automorphism `σ(g)` of `K^form`, and
`IsSymmetry g D` corresponds to `PTSymmetricQFT.QuantumSymmetry.Preserves (σ g) D^form` via `Compatible`
(`D_F(u(g)Φ) = D_{σ(g)F}(Φ)`) — the §2.4 link between field-side and formula-side symmetries.

## References

* H. Greaves, T. Thomas, *The CPT Theorem*, arXiv:1204.4674, §2.3 (Eq. 7, the geometric action; Example 3;
  the internal-symmetry footnote).
* Repo dependencies: `PTSymmetricQFT.QuantumSymmetry` (the formula-side `Preserves`/`Compatible`);
  `PTSymmetricQFT.CPTDiracDynamics`, `PTSymmetricQFT.PTTensorDynamics` (the `g = ` total-inversion instances).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.GeometricAction

variable {G : Type*} [Group G] {M V : Type*} [MulAction G M] [MulAction G V]

/-! ## §A — the geometric action `u(g)Φ = ρ(g) ∘ Φ ∘ ω(g⁻¹)` -/

/-- **[Eq. 7] The geometric action** `u(g)Φ = ρ(g) ∘ Φ ∘ ω(g⁻¹) = fun x ↦ g • Φ (g⁻¹ • x)` — the `V`-action
(`ρ`) on the values, the `M`-action (`ω`) on the argument. -/
def geometricAction (g : G) (Φ : M → V) : M → V := fun x => g • Φ (g⁻¹ • x)

/-- **`u(1) = id`** — the identity acts trivially. -/
theorem geometricAction_one (Φ : M → V) : geometricAction (1 : G) Φ = Φ := by
  funext x; simp [geometricAction]

/-- **`u(gh) = u(g) ∘ u(h)`** — `g ↦ u(g)` is a representation of `G` on the fields `K = M → V`. -/
theorem geometricAction_mul (g h : G) (Φ : M → V) :
    geometricAction (g * h) Φ = geometricAction g (geometricAction h Φ) := by
  funext x; simp only [geometricAction, mul_inv_rev, mul_smul]

/-- `u(g)` is invertible with inverse `u(g⁻¹)`. -/
theorem geometricAction_leftInv (g : G) (Φ : M → V) :
    geometricAction g⁻¹ (geometricAction g Φ) = Φ := by
  rw [← geometricAction_mul, inv_mul_cancel, geometricAction_one]

/-- `u(1) = id` as a function. -/
theorem geometricAction_one' : geometricAction (1 : G) = (id : (M → V) → (M → V)) :=
  funext fun Φ => geometricAction_one Φ

/-- `u(gh) = u(g) ∘ u(h)` as functions. -/
theorem geometricAction_mul' (g h : G) :
    (geometricAction (g * h) : (M → V) → (M → V)) = geometricAction g ∘ geometricAction h :=
  funext fun Φ => geometricAction_mul g h Φ

/-! ## §B — symmetries of a field theory form a subgroup -/

/-- **`g` is a symmetry of `D`**: the geometric action `u(g)` leaves the field theory `D ⊆ K` invariant. -/
def IsSymmetry (g : G) (D : Set (M → V)) : Prop := geometricAction g '' D = D

/-- **[Greaves–Thomas §2.3] The symmetries of a field theory form a subgroup of `G`.** -/
def symmetrySubgroup (D : Set (M → V)) : Subgroup G where
  carrier := {g | IsSymmetry g D}
  one_mem' := by simp only [Set.mem_setOf_eq, IsSymmetry, geometricAction_one', Set.image_id]
  mul_mem' := by
    intro g h hg hh
    simp only [Set.mem_setOf_eq, IsSymmetry] at *
    rw [geometricAction_mul', Set.image_comp, hh, hg]
  inv_mem' := by
    intro g hg
    simp only [Set.mem_setOf_eq, IsSymmetry] at *
    have hcomp : geometricAction g⁻¹ '' (geometricAction g '' D) = D := by
      rw [← Set.image_comp, ← geometricAction_mul', inv_mul_cancel, geometricAction_one',
        Set.image_id]
    rwa [hg] at hcomp

@[simp] theorem mem_symmetrySubgroup {g : G} {D : Set (M → V)} :
    g ∈ symmetrySubgroup D ↔ IsSymmetry g D := Iff.rfl

/-- **`D` is `G`-invariant iff every `g` is a symmetry** — i.e. iff the symmetry subgroup is all of `G`. -/
theorem gInvariant_iff_symmetrySubgroup_top (D : Set (M → V)) :
    (∀ g : G, IsSymmetry g D) ↔ symmetrySubgroup D = (⊤ : Subgroup G) := by
  constructor
  · intro h
    ext g
    simp only [mem_symmetrySubgroup, Subgroup.mem_top, iff_true]
    exact h g
  · intro h g
    have hg : g ∈ symmetrySubgroup D := by rw [h]; exact Subgroup.mem_top g
    exact mem_symmetrySubgroup.mp hg

/-! ## §C — internal vs spacetime symmetries -/

/-- **[Greaves–Thomas §2.3 footnote] Internal symmetry: trivial spacetime action.** When the spacetime
action `ω` is trivial (`g • x = x`), the geometric action is the pointwise value rotation
`u(g)Φ = ρ(g) ∘ Φ` — a global *internal* symmetry. A genuine *spacetime* symmetry has `ω` non-trivial. -/
theorem geometricAction_internal (htriv : ∀ (g : G) (x : M), g • x = x) (g : G) (Φ : M → V) :
    geometricAction g Φ = fun x => g • Φ x := by
  funext x; simp only [geometricAction, htriv]

end Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.GeometricAction

end

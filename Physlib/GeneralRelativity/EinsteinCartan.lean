/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Einstein–Cartan gravity: torsion and the spin coupling

Einstein–Cartan gravity generalizes general relativity by allowing the affine connection to be **non-symmetric**;
its antisymmetric part is the **torsion tensor**

`T^λ_{μν} = Γ^λ_{μν} − Γ^λ_{νμ}`,

antisymmetric in `μν`. The Levi-Civita connection of GR is the torsion-free (symmetric) special case
(`levicivita_is_torsion_free`, `torsion_zero_iff_symmetric`). In Einstein–Cartan theory torsion is **algebraically
sourced by spin**, `T = κ S`; because torsion is antisymmetric, the spin source it carries is antisymmetric too —
the geometric consistency of the spin–torsion coupling.

References: É. Cartan; the Einstein–Cartan(–Sciama–Kibble) theory. No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.GeneralRelativity.EinsteinCartan

/-- **The torsion tensor** `T^λ_{μν} = Γ^λ_{μν} − Γ^λ_{νμ}` — the antisymmetric part of the affine connection. -/
def torsion {κ : Type*} (Γ : κ → κ → κ → ℝ) (l μ ν : κ) : ℝ := Γ l μ ν - Γ l ν μ

/-- **Torsion is antisymmetric** `T^λ_{μν} = −T^λ_{νμ}`. -/
theorem torsion_antisymm {κ : Type*} (Γ : κ → κ → κ → ℝ) (l μ ν : κ) :
    torsion Γ l μ ν = -torsion Γ l ν μ := by
  unfold torsion; ring

/-- **A symmetric connection is torsion-free** — the Levi-Civita connection of general relativity. -/
theorem levicivita_is_torsion_free {κ : Type*} (Γ : κ → κ → κ → ℝ)
    (hsym : ∀ l μ ν, Γ l μ ν = Γ l ν μ) (l μ ν : κ) : torsion Γ l μ ν = 0 := by
  unfold torsion; rw [hsym l μ ν]; ring

/-- **Torsion vanishes iff the connection is symmetric** — Einstein–Cartan reduces to GR exactly when the torsion
is switched off. -/
theorem torsion_zero_iff_symmetric {κ : Type*} (Γ : κ → κ → κ → ℝ) :
    (∀ l μ ν, torsion Γ l μ ν = 0) ↔ (∀ l μ ν, Γ l μ ν = Γ l ν μ) := by
  unfold torsion
  constructor <;> intro h l μ ν <;> have := h l μ ν <;> linarith

/-- **The Einstein–Cartan algebraic torsion equation** `T = κ S` — torsion is non-dynamically sourced by the spin
tensor `S` with coupling `κ`. -/
def EinsteinCartanTorsion {κ' : Type*} (Γ S : κ' → κ' → κ' → ℝ) (kappa : ℝ) : Prop :=
  ∀ l μ ν, torsion Γ l μ ν = kappa * S l μ ν

/-- **The spin source is antisymmetric** `κ S^λ_{μν} = −κ S^λ_{νμ}`. Because torsion is antisymmetric, the
Einstein–Cartan equation `T = κ S` forces the spin source it carries to be antisymmetric in `μν` — the consistency
of the spin–torsion coupling. -/
theorem einsteinCartan_spin_antisymm {κ' : Type*} (Γ S : κ' → κ' → κ' → ℝ) (kappa : ℝ)
    (h : EinsteinCartanTorsion Γ S kappa) (l μ ν : κ') :
    kappa * S l μ ν = -(kappa * S l ν μ) := by
  rw [← h l μ ν, ← h l ν μ, torsion_antisymm]

end Physlib.GeneralRelativity.EinsteinCartan

end

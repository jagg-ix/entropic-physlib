/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Physlib.SpaceAndTime.SpaceTime.Basic

/-!
# Lapse function on spacetime

A `Lapse d` is a strictly-positive scalar function on
`SpaceTime d`, in the ADM sense:

  `N : SpaceTime d → ℝ`, `∀ x, 0 < N x`.

The lapse converts asymptotic-frame quantities to local-frame
quantities at a given event via the Tolman law

  `O_loc(x) := O_∞ / N(x)`,  so that  `O_loc(x) · N(x) = O_∞`.

A thin abstraction over Physlib's existing `SpaceTime d` structure
(built on `Lorentz.Vector d`), so that consumers can take a lapse as
an input parameter without importing additional spacetime machinery.

## Conventions

* Coordinate `0` is time; `1..d` are spatial.
* `Lapse.unit` is the Minkowski-limit lapse `N(x) ≡ 1`.
* `tolman_invariant` is the position-independent identity
  `(O_∞ / N(x)) · N(x) = O_∞`.

## Source and equation map

* R. Arnowitt, S. Deser, and C. W. Misner, *The dynamics of general relativity*,
  in *Gravitation: An Introduction to Current Research* (1962), republished in
  General Relativity and Gravitation 40 (2008), 1997-2027, doi:10.1007/s10714-008-0661-1.
  This is the standard ADM source for using a positive lapse in spacetime splitting.
* R. C. Tolman, *On the Weight of Heat and Thermal Equilibrium in General Relativity*,
  Physical Review 35 (1930), 904-924, doi:10.1103/PhysRev.35.904.
* R. C. Tolman and P. Ehrenfest, *Temperature Equilibrium in a Static Gravitational
  Field*, Physical Review 36 (1930), 1791-1798, doi:10.1103/PhysRev.36.1791.

The Lean structure records only the reusable positive-lapse interface:
`N : SpaceTime d → ℝ`, `0 < N x`. The Tolman expression is represented abstractly as
`O_loc(x) = O_∞ / N(x)`, hence `O_loc(x) * N(x) = O_∞`.
-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace Physlib.SpaceTime

variable {d : ℕ}

/-- **Lapse function** `N : SpaceTime d → ℝ⁺`. -/
structure Lapse (d : ℕ := 3) where
  /-- The lapse value at each spacetime event. -/
  N : SpaceTime d → ℝ
  /-- Lapse is strictly positive everywhere. -/
  N_pos : ∀ x, 0 < N x

namespace Lapse

/-- The **unit lapse** `N(x) ≡ 1` (Minkowski limit, no redshift). -/
def unit : Lapse d where
  N := fun _ => 1
  N_pos := fun _ => one_pos

@[simp] theorem unit_N (x : SpaceTime d) : (unit (d := d)).N x = 1 := rfl

/-- **Tolman invariant**: for any asymptotic value `O_∞` and any
event `x`, the local value `O_loc(x) := O_∞ / N(x)` satisfies
`O_loc(x) · N(x) = O_∞`. -/
theorem tolman_invariant (L : Lapse d) (O_inf : ℝ) (x : SpaceTime d) :
    (O_inf / L.N x) * L.N x = O_inf :=
  div_mul_cancel₀ _ (L.N_pos x).ne'

end Lapse

end Physlib.SpaceTime

end

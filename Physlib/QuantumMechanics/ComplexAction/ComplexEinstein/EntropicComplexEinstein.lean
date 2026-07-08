/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionDampingCoercivity
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations

/-!
# The complex-action/entropic-time entropic damping is sourced by the imaginary Einstein energy

Links the complex-action/entropic-time damping/entropic-time machinery (`PathIntegral.ComplexActionDampingCoercivity`) to the **complex Einstein
equation** (`ComplexEinstein.ComplexMassEinsteinEquations`): the entropic (imaginary) action `S_I` that damps the
path-integral weight is *exactly* the **imaginary Einstein energy** `Im E = m_I c²` accumulated over proper
time — the same `m_R + i·m_I` complex structure underlying both the complex-action/entropic-time complex action `S = S_R + i·S_I`
and the complex Einstein mass.

With `S_I = (Im E)·σ = m_I c²·σ` (`entropicActionEinstein`):

* the **entropic proper time** is `τ_ent = S_I/ℏ = m_I c² σ / ℏ` (`entropicProperTime_einstein`) — the complex-action/entropic-time
  entropic clock *is* the imaginary Einstein energy times proper time;
* the **path-integral damping** is `‖w‖ = exp(−m_I c² σ/ℏ)` (`einstein_entropic_damping`), driven by the
  imaginary mass `m_I`;
* the **reversible limit** `m_I = 0` gives `S_I = 0`, `‖w‖ = 1` (unitary) and `τ_ent = 0`
  (`reversible_einstein_unitary`) — the real standard Einstein equation (`m_I = 0` ⟹ `Im E = 0`), the
  oscillatory-only, dissipation-free case.

So reversible ⟺ real (standard) Einstein ⟺ unitary complex-action/entropic-time weight, and the entropic/dissipative sector is the
imaginary mass `m_I` driving both the GW entropic radiation and the path-integral damping — one `S_R + i·S_I`
decomposition across the gravity, complex-Einstein and complex-action/entropic-time layers.

* **§A — the entropic action from the imaginary Einstein energy** (`entropicActionEinstein`,
  `entropicActionEinstein_eq`, `entropicProperTime_einstein`).
* **§B — the entropic damping** (`einstein_entropic_damping`, `reversible_einstein_unitary`).
* **§C — the unification** (`entropic_complex_einstein_unification`).

## References

* Repo dependencies: `PathIntegral.ComplexActionDampingCoercivity` (`entropicProperTime`, the damping bound),
  `ComplexEinstein.ComplexMassEinsteinEquations` (`complexEinsteinEnergy`, `Im E = m_I c²`),
  `Physlib.QFT.Wick.Consistency` (`complexActionWeight`).

No new axioms.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EntropicComplexEinstein

open Physlib.QFT.Wick.Consistency
open Physlib.QuantumMechanics.ComplexAction.PathIntegral.ComplexActionDampingCoercivity
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations

/-! ## §A — the entropic action from the imaginary Einstein energy -/

/-- **The entropic action from the imaginary Einstein energy** `S_I = (Im E)·σ = m_I c²·σ` — the imaginary
(entropic) part of the complex Einstein energy accumulated over proper time `σ`. -/
noncomputable def entropicActionEinstein (m_R m_I c σ : ℝ) : ℝ :=
  (complexEinsteinEnergy m_R m_I c).im * σ

/-- **`S_I = m_I c²·σ`** — the entropic action in terms of the imaginary mass (`complexEinsteinEnergy_im`). -/
theorem entropicActionEinstein_eq (m_R m_I c σ : ℝ) :
    entropicActionEinstein m_R m_I c σ = m_I * c ^ 2 * σ := by
  rw [entropicActionEinstein, complexEinsteinEnergy_im]

/-- **[The entropic clock is the imaginary Einstein energy] `τ_ent = m_I c² σ / ℏ`** — the complex-action/entropic-time entropic
proper time of the imaginary-Einstein-sourced action is the imaginary mass energy times proper time over `ℏ`. -/
theorem entropicProperTime_einstein (m_R m_I c σ hbar : ℝ) :
    entropicProperTime (entropicActionEinstein m_R m_I c σ) hbar = m_I * c ^ 2 * σ / hbar := by
  rw [entropicProperTime, entropicActionEinstein_eq]

/-! ## §B — the entropic damping driven by the imaginary mass -/

/-- **[Entropic damping from the imaginary mass] `‖w‖ = exp(−m_I c² σ/ℏ)`** — the path-integral weight is
damped by the imaginary Einstein energy; a non-zero `m_I` (entropic/dissipative sector) suppresses the
amplitude. -/
theorem einstein_entropic_damping (S_R m_R m_I c σ hbar : ℝ) :
    ‖complexActionWeight S_R (entropicActionEinstein m_R m_I c σ) hbar‖
      = Real.exp (-(m_I * c ^ 2 * σ / hbar)) := by
  rw [norm_complexActionWeight, entropicActionEinstein_eq]

/-- **[Reversible ⟺ real Einstein ⟺ unitary] `m_I = 0 ⟹ ‖w‖ = 1`.** With no imaginary mass (the real standard
Einstein equation, `Im E = 0`) the entropic action vanishes and the complex-action/entropic-time weight is unitary — the
oscillatory-only, dissipation-free case. -/
theorem reversible_einstein_unitary (S_R m_R c σ hbar : ℝ) :
    ‖complexActionWeight S_R (entropicActionEinstein m_R 0 c σ) hbar‖ = 1 := by
  rw [entropicActionEinstein_eq, norm_complexActionWeight]; simp

/-! ## §C — the unification -/

/-- **[complex-action/entropic-time ↔ complex Einstein, unified] one `S_R + i·S_I` decomposition.** The complex-action/entropic-time entropic proper time
is the imaginary Einstein energy `m_I c² σ/ℏ`; the path-integral damping `‖w‖ = exp(−m_I c² σ/ℏ)` is driven by
the imaginary mass; and the reversible limit `m_I = 0` (the real standard Einstein equation) is the unitary
`‖w‖ = 1` case. The entropic/dissipative sector — the imaginary mass `m_I`, the GW entropic radiation, the
path-integral damping — is one and the same across the gravity, complex-Einstein and complex-action/entropic-time layers. -/
theorem entropic_complex_einstein_unification (S_R m_R m_I c σ hbar : ℝ) :
    entropicProperTime (entropicActionEinstein m_R m_I c σ) hbar = m_I * c ^ 2 * σ / hbar
      ∧ ‖complexActionWeight S_R (entropicActionEinstein m_R m_I c σ) hbar‖
          = Real.exp (-(m_I * c ^ 2 * σ / hbar))
      ∧ ‖complexActionWeight S_R (entropicActionEinstein m_R 0 c σ) hbar‖ = 1 :=
  ⟨entropicProperTime_einstein m_R m_I c σ hbar,
    einstein_entropic_damping S_R m_R m_I c σ hbar,
    reversible_einstein_unitary S_R m_R c σ hbar⟩

end Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EntropicComplexEinstein

end

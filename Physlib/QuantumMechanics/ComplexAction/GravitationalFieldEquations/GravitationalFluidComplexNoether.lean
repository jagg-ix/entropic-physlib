/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.ComplexNoetherChargeEntropicHorizon
public import Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Noether
public import Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSVortexStretchingDefect

/-!
# The complex Noether charge: gravitational Smarr (real) + fluid dissipation (imaginary)

Links the Navier–Stokes enstrophy/Noether kernel (`NavierStokes.NSVortexStretchingDefect`) to the causal-diamond
**Wald–Noether Smarr** derivation (`CausalDiamond.Noether`, §3.1) through the complex-action/entropic-time **complex Noether
charge** (`EntropicTime.ComplexNoetherChargeEntropicHorizon`).

The complex-action/entropic-time complex Noether charge `Q = Re Q − i·Im Q` splits a system into a **real, reversible,
geometric** sector and an **imaginary, dissipative, entropic** sector. The two NS/gravity Noether
quantities are exactly these two sectors:

* the **real part** is the causal-diamond gravitational Noether charge
  `Re Q = noetherCharge = −κA/(8πG)` (`gravFluidNoetherCharge_re`) — the conserved Wald charge that, via
  Stokes `∮Q_ζ = ∫j_ζ`, gives the **Smarr formula** `(d−2)κA = (d−1)κkV + 2V_ζΛ`
  (`gravFluidNoetherCharge_re_smarr`, `smarr_from_noether`);
* the **imaginary part** is half the NS enstrophy rate `Im Q = ½·dΩ/dt = VS − νP`
  (`gravFluidNoetherCharge_im`) — the dissipative fluid sector, the negative of the imaginary Noether
  defect `νP − VS`. It is **non-positive iff the NS regularity criterion `VS ≤ νP` holds**
  (`gravFluidNoetherCharge_im_nonpos_iff`).

So the reversible causal-diamond geometry (the conserved Smarr charge) and the dissipative
Navier–Stokes fluid (the entropy-producing enstrophy rate) are the real and imaginary parts of one
complex Noether charge — the geometric and entropic faces of the complex-action/entropic-time action. (The same `Re/Im`
reversible–entropic split governs the small-diamond Minkowski limit and proper-volume closed forms of
`CausalDiamond.SmallDiamonds` / `CausalDiamond.ProperVolume`.)

* **§A — real = gravitational Smarr charge, imaginary = NS enstrophy rate** (`gravFluidNoetherCharge`,
  `gravFluidNoetherCharge_re`, `gravFluidNoetherCharge_im`).
* **§B — the Smarr formula and the dissipation sign** (`gravFluidNoetherCharge_re_smarr`,
  `gravFluidNoetherCharge_im_nonpos_iff`).
* **§C — the assembly** (`gravitational_fluid_complex_noether`).

## References

* R. M. Wald (Noether-charge entropy); T. Jacobson, M. Visser (causal-diamond Smarr). Carriers:
  `EntropicTime.ComplexNoetherChargeEntropicHorizon` (`complexNoetherCharge`), `CausalDiamond.Noether`
  (`noetherCharge`, `smarr_from_noether`), `NavierStokes.NSVortexStretchingDefect` (`imaginaryNoetherDefect`,
  `enstrophyRate`).


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.GravitationalFieldEquations.GravitationalFluidComplexNoether

open Physlib.QuantumMechanics.ComplexAction.EntropicTime.ComplexNoetherChargeEntropicHorizon
open Physlib.QuantumMechanics.ComplexAction.CausalDiamond.Noether
open Physlib.QuantumMechanics.ComplexAction.NavierStokes.NSVortexStretchingDefect


/-- **The gravitational–fluid complex Noether charge** `Q = noetherCharge − i·(νP − VS)` — the complex-action/entropic-time
complex Noether charge whose real part is the causal-diamond Wald charge `−κA/(8πG)` and whose imaginary
part is the NS imaginary Noether defect. -/
noncomputable def gravFluidNoetherCharge (κ A G ν P VS : ℝ) : ℂ :=
  complexNoetherCharge (noetherCharge κ A G) 1 (imaginaryNoetherDefect ν P VS)

/-- **[Real part = causal-diamond Wald charge] `Re Q = −κA/(8πG)`.** -/
lemma gravFluidNoetherCharge_re (κ A G ν P VS : ℝ) :
    (gravFluidNoetherCharge κ A G ν P VS).re = noetherCharge κ A G := by
  rw [gravFluidNoetherCharge, complexNoetherCharge_re]

/-- **[Imaginary part = half the NS enstrophy rate] `Im Q = ½·dΩ/dt = VS − νP`.** The dissipative fluid
sector is half the Navier–Stokes enstrophy rate (the negative of the imaginary Noether defect). -/
lemma gravFluidNoetherCharge_im (κ A G ν P VS : ℝ) :
    (gravFluidNoetherCharge κ A G ν P VS).im = enstrophyRate VS ν P / 2 := by
  rw [gravFluidNoetherCharge, complexNoetherCharge_im]
  unfold imaginaryNoetherDefect enstrophyRate; ring


/-- **[Real part obeys the Smarr formula] `(d−2)κA = (d−1)κkV + 2V_ζΛ`.** Given the Wald–Noether Stokes
identity `∮Q_ζ = ∫j_ζ` (`hStokes`), the real part of the complex Noether charge — the causal-diamond Wald
charge — satisfies the Smarr formula (`smarr_from_noether`). -/
lemma gravFluidNoetherCharge_re_smarr (κ A k V Λ Vζ d G ν P VS : ℝ) (hπ : (0 : ℝ) < Real.pi)
    (hG : G ≠ 0) (hd : d - 2 ≠ 0)
    (hStokes : noetherCharge κ A G = noetherCurrentIntegral κ k V Λ Vζ d G) :
    (gravFluidNoetherCharge κ A G ν P VS).re = noetherCharge κ A G
      ∧ (d - 2) * κ * A = (d - 1) * κ * k * V + 2 * Vζ * Λ :=
  ⟨gravFluidNoetherCharge_re κ A G ν P VS, smarr_from_noether κ A k V Λ Vζ d G hπ hG hd hStokes⟩

/-- **[The imaginary part is dissipative iff NS-regular] `Im Q ≤ 0 ⟺ VS ≤ νP`.** The fluid sector loses
enstrophy (`Im Q = ½·dΩ/dt ≤ 0`) exactly when the Navier–Stokes regularity criterion holds. -/
lemma gravFluidNoetherCharge_im_nonpos_iff (κ A G ν P VS : ℝ) :
    (gravFluidNoetherCharge κ A G ν P VS).im ≤ 0 ↔ VS ≤ ν * P := by
  rw [gravFluidNoetherCharge_im]
  constructor
  · intro h; exact (enstrophyRate_nonpos_iff VS ν P).mp (by linarith)
  · intro h; have := (enstrophyRate_nonpos_iff VS ν P).mpr h; linarith


/-- **[Gravitational Smarr + fluid dissipation = one complex Noether charge].** The complex-action/entropic-time complex
Noether charge `Q` unifies the two sectors: its **real part** is the causal-diamond Wald charge
`−κA/(8πG)`, which obeys the **Smarr formula** `(d−2)κA = (d−1)κkV + 2V_ζΛ` (the conserved, reversible
gravitational geometry); its **imaginary part** is half the **NS enstrophy rate** `½·dΩ/dt = VS − νP`
(the dissipative, entropy-producing fluid sector), non-positive exactly under the Navier–Stokes
regularity criterion `VS ≤ νP`. The reversible causal-diamond geometry and the dissipative
Navier–Stokes fluid are the real and imaginary parts of one complex Noether charge. -/
lemma gravitational_fluid_complex_noether (κ A k V Λ Vζ d G ν P VS : ℝ) (hπ : (0 : ℝ) < Real.pi)
    (hG : G ≠ 0) (hd : d - 2 ≠ 0)
    (hStokes : noetherCharge κ A G = noetherCurrentIntegral κ k V Λ Vζ d G) :
    (gravFluidNoetherCharge κ A G ν P VS).re = noetherCharge κ A G
      ∧ (d - 2) * κ * A = (d - 1) * κ * k * V + 2 * Vζ * Λ
      ∧ (gravFluidNoetherCharge κ A G ν P VS).im = enstrophyRate VS ν P / 2
      ∧ ((gravFluidNoetherCharge κ A G ν P VS).im ≤ 0 ↔ VS ≤ ν * P) :=
  ⟨gravFluidNoetherCharge_re κ A G ν P VS,
    smarr_from_noether κ A k V Λ Vζ d G hπ hG hd hStokes,
    gravFluidNoetherCharge_im κ A G ν P VS,
    gravFluidNoetherCharge_im_nonpos_iff κ A G ν P VS⟩

end Physlib.QuantumMechanics.ComplexAction.GravitationalFieldEquations.GravitationalFluidComplexNoether

end

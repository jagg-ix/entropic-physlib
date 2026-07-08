/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EntropicComplexEinstein
public import Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.DiamondTimeReversal
public import Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification

/-!
# How and where the imaginary mass enters: the dissipative sector and its BCJ image

The complex mass `m = m_R + i m_I` of the Nagao–Nielsen / complex-Einstein framework splits the physics in
two. This module pins down, as theorems, exactly **where** the imaginary mass `m_I` enters and where it
does not, and identifies its image under the **BCJ double copy**.

* **§A — the imaginary mass lives in the dissipative sector.** `imaginaryMass_dissipative_not_geometric`:
 `m_I` enters the entropic action `S_I = m_I c² σ` (`EntropicComplexEinstein.entropicActionEinstein_eq`),
 and through it damps the path-integral weight `‖w‖ = exp(−m_I c² σ/ℏ)` (`imaginaryMass_damps_weight`,
 from `einstein_entropic_damping`), while the geometric mass-shell `(mc)²`
 (`NagaoNielsenMassShellCone.tetrad_massShell_uses_real_mass`, tetrad-gauged) depends only on the real
 mass `m_R`. So `m_I` is confined to the imaginary/dissipative sector and never touches the real geometry.
* **§B — the BCJ image: the imaginary sector is the T-odd numerator.** In `BCJDoubleCopy.DiamondTimeReversal`
 the diamond triple `(n, c, D) = (sinh θ, sinh θ, cosh²θ)` has the **mass-shell propagator** `D` T-even
 and the **entropic numerator** `n` T-odd (`bcj_massShell_Teven_imaginary_Todd`) — the same real/imaginary
 split. The double copy `n²/D = tanh²θ = (e^{−S_I/ℏ})²` (`bcj_doublecopy_is_suppression_squared`) is the
 entanglement suppression **squared**: the imaginary/entropic sector enters gravity squared, because
 gravity is gauge².

The scalar identities are exact and reuse the existing modules; the reading of `m_I`
as the dissipative sector and of `sinh θ` as its BCJ numerator (the "numerators identified as
imaginary/entropic actions" of `ColorKinematicsDoubleCopy`) is the interpretive framework.
-/

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ImaginaryMassDissipativeBCJ

open Physlib.QFT.Wick.Consistency
open Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone
open Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.EntropicComplexEinstein
open Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.DiamondTimeReversal
open Physlib.QuantumMechanics.ComplexAction.MuonAnomaly.SchmidtRapidityHyperbolicUnification

/-! ## §A — the imaginary mass lives in the dissipative sector, not the geometry -/

/-- **[Where the imaginary mass enters and does not]** the imaginary mass `m_I` sets the entropic action
`S_I = m_I c² σ`, while the geometric mass-shell `(mc)²` depends only on the real mass `m_R`: `m_I` is in
the dissipative/imaginary sector, `m_R` in the real geometry. -/
theorem imaginaryMass_dissipative_not_geometric (m_R m_I c σ p : ℝ) (hc : c ≠ 0) :
    entropicActionEinstein m_R m_I c σ = m_I * c ^ 2 * σ
      ∧ nnLorentzForm (energyMomentumComplex m_R c p) = (m_R * c) ^ 2 :=
  ⟨entropicActionEinstein_eq m_R m_I c σ, tetrad_massShell_uses_real_mass m_R c p hc⟩

/-- **[How the imaginary mass enters]** through the entropic action it damps the path-integral weight,
`‖w‖ = exp(−m_I c² σ/ℏ)`: a nonzero `m_I` (the imaginary/entropic sector) exponentially suppresses the
amplitude, while `m_I = 0` (real Einstein) leaves it unitary. -/
theorem imaginaryMass_damps_weight (S_R m_R m_I c σ hbar : ℝ) :
    ‖complexActionWeight S_R (entropicActionEinstein m_R m_I c σ) hbar‖
      = Real.exp (-(m_I * c ^ 2 * σ / hbar)) :=
  einstein_entropic_damping S_R m_R m_I c σ hbar

/-! ## §B — the BCJ image: the imaginary sector is the T-odd numerator, squared into gravity -/

/-- **[The real/imaginary split is the BCJ propagator/numerator split]** the diamond BCJ propagator (the
mass shell, `cosh²θ`) is time-reversal even, the entropic numerator (`sinh θ`) is time-reversal odd — the
mass-shell/real-mass sector versus the entropic/imaginary-mass sector. -/
theorem bcj_massShell_Teven_imaginary_Todd (θ : ℝ) :
    (diamondBCJTriple (-θ)).propagator = (diamondBCJTriple θ).propagator
      ∧ (diamondBCJTriple (-θ)).numerator = -(diamondBCJTriple θ).numerator :=
  ⟨diamondBCJ_propagator_timeReversal θ, diamondBCJ_numerator_timeReversal θ⟩

/-- **[The double copy squares the entropic suppression]** `n²/D = (e^{−S_I/ℏ})²`. The diamond BCJ
double-copy diagonal `tanh²θ` (`diamondBCJ_diagonal`) equals the *square* of the entanglement suppression
`e^{−S_I/ℏ} = tanh η` (`suppression_eq_tanh`) — the imaginary/entropic sector enters the gravity double copy
squared, because gravity is gauge². -/
theorem bcj_doublecopy_is_suppression_squared (ħ η : ℝ) (hħ : ħ ≠ 0) (hη : 0 < η) :
    (diamondBCJTriple η).numerator ^ 2 / (diamondBCJTriple η).propagator
      = Real.exp (-(entropicAction ħ η / ħ)) ^ 2 := by
  rw [diamondBCJ_diagonal, suppression_eq_tanh ħ η hħ hη]

end Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ImaginaryMassDissipativeBCJ

end

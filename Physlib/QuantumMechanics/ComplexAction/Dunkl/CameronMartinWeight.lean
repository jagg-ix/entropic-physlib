/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.Dunkl.EmbeddingMatsubaraConsistency
public import Physlib.QuantumMechanics.NonHermitian.WickRotation
meta import Zil

/-!
# The Cameron–Martin weight `W = e^{−S_I/ℏ}` along the stochastic Lagrangian paths of the Dunkl process

Completes the Wigner–Dunkl path-integral arc by establishing the **Cameron–Martin weight**
`W = e^{−S_I/ℏ}` *evaluated along the stochastic Lagrangian paths* of the Dunkl process (Junker §5; the
Cameron–Martin / Cameron–Storvick Wiener–Feynman correspondence, refs [43,44]). The stochastic Lagrangian
paths are the reflecting/absorbing Bessel (Wiener) trajectories `z(τ)` of `Dunkl.EuclideanProcess`;
the weight is the pathwise Feynman–Kac factor `fkPathWeight V z t = exp(−∫₀^t V(z τ) dτ)`.

The point is that the *pathwise imaginary action* accumulated along the stochastic trajectory,
`S_I/ℏ = ∫₀^t V(z τ) dτ` (the cumulative Lagrangian potential along the path), is what enters the
Cameron–Martin weight, and that `W = e^{−S_I/ℏ}` is exactly the entropic damping
(`WickRotation.entropyDamping`) and the modulus of the complex path integral evaluated path by path.

* **§A** `cameronMartinWeight`, `pathwiseImaginaryAction` — the weight and the pathwise `S_I` along `z`.
* **§B** `cameronMartin_eq_entropyDamping` — `W = e^{−S_I/ℏ}` along the stochastic Lagrangian path, with
  `S_I = ℏ·∫₀^t V(z τ) dτ`. This is the precise statement requested.
* **§C** `cameronMartin_eq_complexNorm` — `W` is the modulus of the complex (Lorentzian) path-integral
  kernel evaluated along the path: `W = ‖lorentzianKernel S_R S_I ℏ‖`.
* **§D** `cameronMartin_pos`, `cameronMartin_le_one`, `cameronMartin_free` — strictly positive, a
  sub-probability (`≤ 1`) for `V ≥ 0` (Radon–Nikodym/Girsanov density reweighting the free Bessel measure),
  and `= 1` on the free path (`V = 0`).
* **§E** `cameronMartin_eq_exp_neg_entropicTime` — `W = e^{−τ_ent}` with the pathwise entropic time
  `τ_ent = ∫₀^t V(z τ) dτ`, the stochastic-path form of the scalar Cameron weight
  `euclideanCameronWeight = exp(−entropicRate)`.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Dunkl.CameronMartinWeight

open Physlib.QFT.PathIntegral
open Physlib.QuantumMechanics.NonHermitian.WickRotation


/-- **The Cameron–Martin weight along a stochastic Lagrangian path** `z(τ)`: the pathwise Feynman–Kac
factor `W = exp(−∫₀^t V(z τ) dτ)`. The path `z` is a reflecting/absorbing Bessel (Wiener) trajectory of
the Dunkl process (`Dunkl.EuclideanProcess`); `W` reweights the free Bessel measure to the
interacting one (the Cameron–Martin / Girsanov Radon–Nikodym density). -/
noncomputable def cameronMartinWeight (V : ℝ → ℝ) (z : ℝ → ℝ) (t : ℝ) : ℝ := fkPathWeight V z t

/-- **The pathwise imaginary action** `S_I = ℏ·∫₀^t V(z τ) dτ` accumulated along the stochastic Lagrangian
path `z`. Its scaled value `S_I/ℏ` is the cumulative Lagrangian potential along the trajectory. -/
noncomputable def pathwiseImaginaryAction (V : ℝ → ℝ) (z : ℝ → ℝ) (t ℏ : ℝ) : ℝ :=
  ℏ * fkPathPotential V z t

/-- `W = exp(−∫₀^t V(z τ) dτ)` — the Cameron–Martin weight unfolds to the pathwise exponential. -/
lemma cameronMartinWeight_eq (V : ℝ → ℝ) (z : ℝ → ℝ) (t : ℝ) :
    cameronMartinWeight V z t = Real.exp (-(fkPathPotential V z t)) := rfl


/-- **[Main] The Cameron–Martin weight is `W = e^{−S_I/ℏ}` evaluated along the stochastic Lagrangian
path.** With the pathwise imaginary action `S_I = ℏ·∫₀^t V(z τ) dτ`, the weight equals the entropic
damping `entropyDamping S_I ℏ = e^{−S_I/ℏ}`. So `W` is precisely `e^{−S_I/ℏ}` with the imaginary action
read off the stochastic trajectory `z` (the cumulative Lagrangian potential along the path). -/
lemma cameronMartin_eq_entropyDamping (V : ℝ → ℝ) (z : ℝ → ℝ) (t ℏ : ℝ) (hℏ : ℏ ≠ 0) :
    cameronMartinWeight V z t = entropyDamping (pathwiseImaginaryAction V z t ℏ) ℏ := by
  unfold cameronMartinWeight fkPathWeight entropyDamping pathwiseImaginaryAction
  congr 1; field_simp


/-- **[Bridge] The Cameron–Martin weight is the modulus of the complex (Lorentzian) path-integral kernel
along the path.** `W = ‖lorentzianKernel S_R S_I ℏ‖` with `S_I = ℏ·∫₀^t V(z τ) dτ` — the entropic damping
that the complex path integral's modulus reduces to, evaluated path by path. The reversible phase `S_R`
drops out of the modulus, leaving the Cameron–Martin weight. -/
lemma cameronMartin_eq_complexNorm (V : ℝ → ℝ) (z : ℝ → ℝ) (t ℏ S_R : ℝ) (hℏ : ℏ ≠ 0) :
    ‖lorentzianKernel S_R (pathwiseImaginaryAction V z t ℏ) ℏ‖ = cameronMartinWeight V z t := by
  rw [lorentzianKernel_norm_is_damping]
  unfold cameronMartinWeight fkPathWeight pathwiseImaginaryAction
  congr 1; field_simp


/-- The Cameron–Martin weight is strictly positive. -/
lemma cameronMartin_pos (V : ℝ → ℝ) (z : ℝ → ℝ) (t : ℝ) : 0 < cameronMartinWeight V z t :=
  fkPathWeight_pos V z t

/-- **The Cameron–Martin weight is a sub-probability density** (`≤ 1`) for `V ≥ 0`, `t ≥ 0`: it reweights
the free Bessel (Wiener) measure to the interacting Dunkl process without increasing mass — a genuine
Radon–Nikodym/Girsanov density. -/
lemma cameronMartin_le_one (V : ℝ → ℝ) (z : ℝ → ℝ) (t : ℝ) (hV : ∀ y, 0 ≤ V y) (ht : 0 ≤ t) :
    cameronMartinWeight V z t ≤ 1 :=
  fkPathWeight_le_one V z t hV ht

/-- **On the free path (`V = 0`) the Cameron–Martin weight is `1`**: no reweighting — the Dunkl process
reduces to the bare reflecting/absorbing Bessel processes. -/
lemma cameronMartin_free (z : ℝ → ℝ) (t : ℝ) : cameronMartinWeight (fun _ => 0) z t = 1 := by
  unfold cameronMartinWeight
  exact Dunkl.EuclideanProcess.dunkl_fk_free_weight z t


/-- **`W = e^{−τ_ent}` with the pathwise entropic time** `τ_ent = ∫₀^t V(z τ) dτ`. The Cameron–Martin
weight along the stochastic Lagrangian path is the exponential of the entropy produced along that
trajectory — the stochastic-path generalization of the scalar Cameron weight
`euclideanCameronWeight = exp(−entropicRate)` (whose docstring fixes `W = exp(−τ_ent)`, `S_I = τ_ent·ℏ`). -/
lemma cameronMartin_eq_exp_neg_entropicTime (V : ℝ → ℝ) (z : ℝ → ℝ) (t : ℝ) :
    cameronMartinWeight V z t = Real.exp (-(fkPathPotential V z t)) :=
  cameronMartinWeight_eq V z t

end Physlib.QuantumMechanics.ComplexAction.Dunkl.CameronMartinWeight

end

/- ZIL-BEGIN -/

zil attach Physlib.QuantumMechanics.ComplexAction.Dunkl.CameronMartinWeight.cameronMartin_eq_entropyDamping where
  formalizes @ "claim:the-pathwise-cameron-martin-weight-equals-the-entropic-damping-factor-exp-minus-imaginary-action-over-hbar",
  supported_by @ "paper:feynman-kac-girsanov-cameron-martin-density"

zil attach Physlib.QuantumMechanics.ComplexAction.Dunkl.CameronMartinWeight.cameronMartin_eq_complexNorm where
  supported_by @ "lean:Physlib.QFT.PathIntegral.lorentzianKernel_norm_is_damping",
  formalizes @ "claim:the-cameron-martin-weight-is-the-modulus-of-the-complex-lorentzian-path-integral-kernel-the-reversible-phase-drops-out",
  requires @ "claim:the-pathwise-cameron-martin-weight-equals-the-entropic-damping-factor-exp-minus-imaginary-action-over-hbar"

zil attach Physlib.QuantumMechanics.ComplexAction.Dunkl.CameronMartinWeight.cameronMartin_le_one where
  supported_by @ "lean:Physlib.QFT.PathIntegral.fkPathWeight_le_one",
  formalizes @ "claim:for-a-nonnegative-potential-the-cameron-martin-weight-is-a-sub-probability-density-mass-non-increasing"

zil attach Physlib.QuantumMechanics.ComplexAction.Dunkl.CameronMartinWeight.cameronMartin_free where
  supported_by @ "lean:TwoStateErasureSetup.with",
  formalizes @ "claim:on-the-free-path-the-cameron-martin-weight-is-one-no-reweighting"

zil_file_contract physlib.cameronMartinWeight where
  promises "The Dunkl-process Cameron-Martin weight: the pathwise Feynman-Kac / Girsanov density W = exp(-int V dtau) reweighting the free Bessel measure to the interacting one is exactly the entropic-damping factor e^{-S_I/hbar} read off the stochastic path, equals the modulus of the complex Lorentzian path-integral kernel (the reversible phase drops out), is a strictly positive sub-probability density for nonnegative potentials, and reduces to one on the free path."
  at_level bridge_theorem
  contract_status satisfied
  requires_objects ["lean:Physlib.QuantumMechanics.ComplexAction.Dunkl.CameronMartinWeight.cameronMartinWeight",
    "lean:Physlib.QuantumMechanics.ComplexAction.Dunkl.CameronMartinWeight.pathwiseImaginaryAction"]
  forbids_substitutes ["any measure-theoretic Girsanov theorem, the density here is the pathwise Feynman-Kac factor not a Radon-Nikodym derivative of measures"]
  witnessed_by [Physlib.QuantumMechanics.ComplexAction.Dunkl.CameronMartinWeight.cameronMartin_eq_entropyDamping,
    Physlib.QuantumMechanics.ComplexAction.Dunkl.CameronMartinWeight.cameronMartin_eq_complexNorm,
    Physlib.QuantumMechanics.ComplexAction.Dunkl.CameronMartinWeight.cameronMartin_le_one,
    Physlib.QuantumMechanics.ComplexAction.Dunkl.CameronMartinWeight.cameronMartin_free,
    Physlib.QuantumMechanics.ComplexAction.Dunkl.CameronMartinWeight.cameronMartin_pos]

/- ZIL-END -/

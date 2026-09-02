/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Mathlib.Data.ZMod.Basic

/-!
# The AdS/C-P-T correspondence: S-duality on the discrete C, P, T symmetries

Following **J. Gomis, "The AdS/C-P-T Correspondence"** (arXiv:2507.12467): the discrete `C`, `P`, `T`
(charge-conjugation, parity, time-reversal) global symmetries of `𝒩 = 4` SYM are identified with bulk (gauge)
symmetries of Type IIB string theory on `AdS₅ × S⁵`, and under **`S`-duality** (with an `SU(4)` R-symmetry outer
automorphism) they transform as

`P ↦ CP,   T ↦ CT,   C ↦ C,   CPT ↦ CPT`.

This module formalizes that discrete-symmetry action.  Writing a symmetry as its `(C, P, T)` charge vector in
`(ℤ/2)³`, the `S`-duality map is the linear involution

`σ(c, p, t) = (c + p + t, p, t)`,

which realizes exactly the transformation above:

* `sDuality_charge_conjugation` — `σ(C) = C` (`C` is `S`-invariant);
* `sDuality_parity` — `σ(P) = CP` (parity maps to `CP`);
* `sDuality_time_reversal` — `σ(T) = CT` (time-reversal maps to `CT`);
* `sDuality_CPT_invariant` — `σ(CPT) = CPT` (**`CPT` is `S`-invariant** — the anchor of the correspondence);
* `sDuality_involutive` — `σ² = id` (`S²` acts trivially on the `C, P, T` group).

This is the discrete-symmetry heart of the arc's `C, P, T` structure: `C` is the electron→positron
charge-conjugate mirror trefoil (`Particles.PositronModel`, `SciamaGravitoYangMillsTrefoilString`), `CPT` is the
invariance of the complex-mass Dirac dynamics (`SciamaUnruhComplexEinsteinFermion`,
`positron_dirac_cpt_invariant`), and `S`-duality is the `BCJ` / `gravity = gauge²` self-duality
(`SciamaFockBCJAdSCFT`) that relates the `𝒩 = 4` gauge theory to its dual — the AdS/CFT bridge of
`SciamaFockAdSCFT`.

Honest scope: the `(ℤ/2)³` group action of `S`-duality on `C, P, T` (the paper's discrete-symmetry table).  The
full AdS₅×S⁵ bulk realization, the charge-conjugation monodromy defects, and the worldsheet vs target-space
symmetry analysis are the paper's content, contextualized here.
-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTCorrespondence

/-- A discrete `C`/`P`/`T` symmetry as its charge vector `(c, p, t)` in `(ℤ/2)³`. -/
abbrev CPTCharge : Type := ZMod 2 × ZMod 2 × ZMod 2

/-- Charge conjugation `C = (1, 0, 0)`. -/
def chargeC : CPTCharge := (1, 0, 0)

/-- Parity `P = (0, 1, 0)`. -/
def chargeP : CPTCharge := (0, 1, 0)

/-- Time reversal `T = (0, 0, 1)`. -/
def chargeT : CPTCharge := (0, 0, 1)

/-- The `CPT` element `= (1, 1, 1)`. -/
def chargeCPT : CPTCharge := (1, 1, 1)

/-- **`S`-duality on the `C, P, T` charges** `σ(c, p, t) = (c + p + t, p, t)` — the linear involution realizing
`P ↦ CP`, `T ↦ CT`, `C ↦ C`. -/
def sDuality (x : CPTCharge) : CPTCharge := (x.1 + x.2.1 + x.2.2, x.2.1, x.2.2)

/-- **[C is S-invariant] `σ(C) = C`.** -/
theorem sDuality_charge_conjugation : sDuality chargeC = chargeC := by decide

/-- **[Parity maps to CP] `σ(P) = CP`.** -/
theorem sDuality_parity : sDuality chargeP = chargeC + chargeP := by decide

/-- **[Time-reversal maps to CT] `σ(T) = CT`.** -/
theorem sDuality_time_reversal : sDuality chargeT = chargeC + chargeT := by decide

/-- **[CPT is S-invariant] `σ(CPT) = CPT`.**  The `CPT` symmetry is preserved by `S`-duality — the anchor of the
AdS/C-P-T correspondence. -/
theorem sDuality_CPT_invariant : sDuality chargeCPT = chargeCPT := by decide

/-- **[S² acts trivially] `σ(σ(x)) = x`.**  `S`-duality is an involution on the `C, P, T` symmetry group. -/
theorem sDuality_involutive (x : CPTCharge) : sDuality (sDuality x) = x := by
  revert x
  decide

end Physlib.QuantumMechanics.ComplexAction.Lorentz.SciamaAdSCPTCorrespondence

end

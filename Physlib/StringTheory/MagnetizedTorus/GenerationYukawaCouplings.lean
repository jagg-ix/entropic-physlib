/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.Particles.FlavorPhysics.CKMMatrix.Basic
public import Physlib.QuantumMechanics.ComplexAction.Yukawa.SeesawMass
public import Physlib.QuantumMechanics.ComplexAction.Yukawa.MassDecoherenceProportionality
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Generation structures and Yukawa couplings in magnetized torus models

This file formalizes the finite algebraic layer of Jeric--Kobayashi--Nasu--Takada,
*Generation structures and Yukawa couplings in magnetized `T^{2g}/Z_N` models*,
arXiv:2507.05645v1.

The analytic theta-function overlap integral is not asserted here.  Instead this module records the
parts that are already finite and checkable in Lean:

* the Higgs-sector flux is the sum of the left- and right-sector fluxes, `N_H = N_L + N_R`
  (paper Eq. (83));
* simultaneously diagonalized flux matrices commute, matching the paper's use of commuting
  `N_L`, `N_R`, `M_L`, `M_R` in the product formula;
* the index selection rule from integrating the product over the torus, namely
  `(N_L + N_R) k = N_L i + N_R j + N_L m` (paper Eq. (253));
* a selected Yukawa overlap amplitude that is forced to vanish when that selection rule fails;
* the resulting three-generation carrier `Fin 3` is the same generation index shape used by the
  CKM formalization, and real overlap entries feed the existing Yukawa-mass/seesaw infrastructure.


-/

set_option autoImplicit false

@[expose] public section

namespace Physlib.StringTheory.MagnetizedTorus.GenerationYukawaCouplings

open Matrix

/-! ## Basic flux and generation carriers -/

/-- A magnetic flux matrix on a `T^{2g}` compactification, represented by its integer matrix. -/
abbrev FluxMatrix (g : Nat) := Matrix (Fin g) (Fin g) ℤ

/-- Integer labels for the theta-function zero-mode lattice in a `g`-dimensional complex torus. -/
abbrev ModeLabel (g : Nat) := Fin g → ℤ

/-- The three light generations use the same finite carrier as CKM matrices. -/
abbrev Generation := Fin 3

/-- A three-generation Yukawa texture. -/
abbrev ThreeGenerationYukawaTexture (R : Type) := Matrix Generation Generation R

/-- The zero-mode degeneracy associated with a flux matrix, modeled by the absolute determinant. -/
def zeroModeDegeneracy {g : Nat} (N : FluxMatrix g) : Nat := Int.natAbs N.det

@[simp] lemma generation_card : Fintype.card Generation = 3 := by rfl

/-! ## Flux additivity and commuting diagonal fluxes -/

/-- The Higgs-sector magnetic flux forced by gauge invariance: `N_H = N_L + N_R`. -/
def higgsFlux {g : Nat} (NL NR : FluxMatrix g) : FluxMatrix g := NL + NR

/-- A left/right/Higgs flux triple satisfying the paper's gauge-invariance condition. -/
def GaugeInvariantFluxTriple {g : Nat} (NL NR NH : FluxMatrix g) : Prop :=
  NH = higgsFlux NL NR

@[simp]
lemma gaugeInvariant_higgsFlux {g : Nat} (NL NR : FluxMatrix g) :
    GaugeInvariantFluxTriple NL NR (higgsFlux NL NR) := rfl

lemma GaugeInvariantFluxTriple.higgs_eq_left_add_right {g : Nat}
    {NL NR NH : FluxMatrix g} (h : GaugeInvariantFluxTriple NL NR NH) :
    NH = NL + NR := h

/-- A diagonalized flux matrix.  This is the basis used after simultaneous diagonalization. -/
def diagonalFlux {g : Nat} (q : Fin g → ℤ) : FluxMatrix g := diagonal q

@[simp]
lemma diagonalFlux_mul {g : Nat} (q r : Fin g → ℤ) :
    diagonalFlux q * diagonalFlux r = diagonalFlux (fun i => q i * r i) := by
  simp [diagonalFlux, Matrix.diagonal_mul_diagonal]

/-- Simultaneously diagonalized integer fluxes commute. -/
lemma diagonalFlux_commute {g : Nat} (q r : Fin g → ℤ) :
    diagonalFlux q * diagonalFlux r = diagonalFlux r * diagonalFlux q := by
  rw [diagonalFlux_mul, diagonalFlux_mul]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [diagonalFlux, mul_comm]
  · simp [diagonalFlux, Matrix.diagonal_apply_ne _ hij]

/-! ## Yukawa selection rule -/

/-- The finite index selection rule obtained from the `x`-integral in the Yukawa overlap.

This is the algebraic content of paper Eq. (253):
`(N_L + N_R) k = N_L i + N_R j + N_L m`.
-/
def YukawaSelectionRule {g : Nat} (NL NR : FluxMatrix g)
    (i j k m : ModeLabel g) : Prop :=
  (higgsFlux NL NR) *ᵥ k = NL *ᵥ i + NR *ᵥ j + NL *ᵥ m

lemma yukawaSelectionRule_iff {g : Nat} (NL NR : FluxMatrix g)
    (i j k m : ModeLabel g) :
    YukawaSelectionRule NL NR i j k m ↔
      (NL + NR) *ᵥ k = NL *ᵥ i + NR *ᵥ j + NL *ᵥ m := Iff.rfl

@[simp]
lemma yukawaSelectionRule_zeroInsertion_iff {g : Nat} (NL NR : FluxMatrix g)
    (i j k : ModeLabel g) :
    YukawaSelectionRule NL NR i j k 0 ↔
      (NL + NR) *ᵥ k = NL *ᵥ i + NR *ᵥ j := by
  simp [YukawaSelectionRule, higgsFlux]

/-- A selected Yukawa overlap coefficient: it carries an arbitrary analytic coefficient `base`, but
enforces the finite torus selection rule exactly. -/
noncomputable def selectedYukawaOverlap {g : Nat} (base : ℂ) (NL NR : FluxMatrix g)
    (i j k m : ModeLabel g) : ℂ := by
  classical
  exact if YukawaSelectionRule NL NR i j k m then base else 0

@[simp]
lemma selectedYukawaOverlap_of_selection {g : Nat} {base : ℂ} {NL NR : FluxMatrix g}
    {i j k m : ModeLabel g} (h : YukawaSelectionRule NL NR i j k m) :
    selectedYukawaOverlap base NL NR i j k m = base := by
  classical
  simp [selectedYukawaOverlap, h]

@[simp]
lemma selectedYukawaOverlap_of_not_selection {g : Nat} {base : ℂ} {NL NR : FluxMatrix g}
    {i j k m : ModeLabel g} (h : ¬ YukawaSelectionRule NL NR i j k m) :
    selectedYukawaOverlap base NL NR i j k m = 0 := by
  classical
  simp [selectedYukawaOverlap, h]

/-- If the torus index rule fails, the selected overlap vanishes. -/
lemma noSelection_yukawaOverlap_zero {g : Nat} (base : ℂ) (NL NR : FluxMatrix g)
    (i j k m : ModeLabel g) (h : ¬ YukawaSelectionRule NL NR i j k m) :
    selectedYukawaOverlap base NL NR i j k m = 0 :=
  selectedYukawaOverlap_of_not_selection h

/-! ## Three-generation and CKM/Yukawa-mass links -/

/-- The CKM entry indexed by the same `Fin 3` generation carrier used for three-mode textures. -/
def ckmEntry (V : CKMMatrix) (i j : Generation) : ℂ := V.1 i j

@[simp] lemma ckmEntry_eq (V : CKMMatrix) (i j : Generation) :
    ckmEntry V i j = V.1 i j := rfl

/-- A real magnetized-torus overlap entry used as a Standard-Model Yukawa coupling. -/
noncomputable def realOverlapYukawaMass (Y : ThreeGenerationYukawaTexture ℝ)
    (v : ℝ) (i j : Generation) : ℝ :=
  _root_.Physlib.QuantumMechanics.ComplexAction.Yukawa.SeesawMass.yukawaMass (Y i j) v

/-- The existing Yukawa-mass theorem applies entrywise to a real magnetized-torus overlap texture. -/
lemma realOverlapYukawaMass_sq (Y : ThreeGenerationYukawaTexture ℝ)
    (v : ℝ) (i j : Generation) :
    realOverlapYukawaMass Y v i j ^ 2 = (Y i j) ^ 2 * v ^ 2 / 2 := by
  exact _root_.Physlib.QuantumMechanics.ComplexAction.Yukawa.SeesawMass.yukawaMass_sq (Y i j) v

/-- The existing entropy-width identity applies entrywise to a real magnetized-torus overlap texture. -/
lemma realOverlapYukawaWidth_eq_widthFromRate
    (Y : ThreeGenerationYukawaTexture ℝ) (ω₀ ℏ : ℝ) (i j : Generation) :
    _root_.Physlib.QuantumMechanics.ComplexAction.Yukawa.MassDecoherenceProportionality.yukawaDecoherenceWidth
        (Y i j) ω₀ ℏ =
      _root_.Physlib.QuantumMechanics.ComplexAction.widthFromRate
        (_root_.Physlib.QuantumMechanics.ComplexAction.Yukawa.MassDecoherenceProportionality.yukawaEntropyRate
          (Y i j) ω₀ ℏ) := by
  exact _root_.Physlib.QuantumMechanics.ComplexAction.Yukawa.MassDecoherenceProportionality.yukawaWidth_eq_widthFromRate_entropyRate
    (Y i j) ω₀ ℏ

end Physlib.StringTheory.MagnetizedTorus.GenerationYukawaCouplings

end

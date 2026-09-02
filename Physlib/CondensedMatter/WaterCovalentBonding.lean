/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

public import Physlib.QuantumMechanics.ComplexAction.PeriodicTableAufbauStructure
public import Physlib.QuantumMechanics.ComplexAction.Su5StandardModelAnomalyFree
public import Physlib.QuantumMechanics.ComplexAction.Bogoliubov.CARAlgebraAutomorphism
public import Physlib.QuantumMechanics.ComplexAction.TetrahedralLorentzFrame
public import Physlib.QuantumMechanics.ComplexAction.IcosahedralStressEnergyAction
public import Physlib.FluidDynamics.BubblePairLocalFrame

/-!
# Hydrogen, oxygen, and the covalent bond — from particle charges and second quantization to the water medium

`FluidDynamics.BubblePairLocalFrame` treats the bubble pair macroscopically: the medium enters only
through the density, viscosity, and surface tension of the Weber–Reynolds control plane. This module
descends one level: the medium is *water*, and its surface tension is a molecular-bonding quantity.
The chain runs from the particle content of the atoms through the second-quantized covalent bond to
the geometry and symmetry of the hydrogen-bond network, each stage on an existing arc of the library.

* **§A — hydrogen and oxygen.** From the aufbau structure
  (`PeriodicTableAufbauStructure.cumulativeCapacity`, `noble_gas_numbers`): hydrogen (`Z = 1`) is one
  electron short of helium (`hydrogen_monovalent`), oxygen (`Z = 8`) two short of neon
  (`oxygen_divalent`), and octet closure *forces* the water stoichiometry — the number of hydrogens
  whose single electrons fill oxygen's holes is uniquely `2` (`water_stoichiometry`), and uniquely
  `4` for carbon (`methane_stoichiometry`, the molecule of `TetrahedralNuclearSpinWeights`). On the
  particle side (`Su5StandardModelAnomalyFree`): the hydrogen nucleus is the `uud` proton — a colour
  singlet by `ColorSingletBaryon` — whose SU(5)-quantized charges sum to `+1`
  (`proton_charge_quantized`) with unit baryon number (`proton_baryon_one`), so the hydrogen atom,
  and every `Z`-proton/`Z`-electron atom (oxygen at `Z = 8`), is exactly neutral
  (`hydrogen_neutral`, `atom_neutral`) — charge quantization is why molecules are neutral objects
  whose residual interactions are the hydrogen bonds of §C–§D.

* **§B — the covalent bond in second quantization.** On the CAR carrier
  (`Bogoliubov.CARAlgebraAutomorphism.IsCAR`): for orthonormal one-particle orbitals `f` (H `1s`) and
  `g` (O `2p`), the LCAO combinations `(f ± g)/√2` are the **bonding and antibonding orbitals**
  (`bondingOrbital`, `antibondingOrbital`); they are again orthonormal
  (`bondingOrbital_normalized`, `bonding_antibonding_orthogonal`), so the smeared modes
  `B(bond), B(antibond)` satisfy the CAR exactly (`bondingMode_CAR`, `bonding_antibonding_CAR`) —
  the two-mode instance of `bogoliubov_preserves_CAR` and of the dead-wood basis change
  (`ConfigurationSpaceDiracFluctuation.basisChange_CAR_kernel`, `seaMode`). Pauli exclusion on the
  bond is exact: `B(bond)² = 0` (`bondingMode_pauli`) — one electron per spin channel, the *shared
  pair*. The LCAO Hamiltonian diagonalizes in this basis as an exact operator identity:
  `ε(a†a + b†b) − t(a†b + b†a) = (ε−t)·p†p + (ε+t)·m†m` (`lcao_diagonalization`) — the bonding
  orbital lies lower by `2t`, which *is* the covalent bond energy.

* **§C — the geometry: sp³ legs and the clathrate cage.** Oxygen's four sp³ hybrids point along the
  tetrahedral legs of `TetrahedralLorentzFrame.tetraVec`: the ideal bond angle satisfies
  `cos θ = ⟪vᵢ,vⱼ⟫/⟪vᵢ,vᵢ⟫ = −1/3` (`sp3_bond_angle_cos`, reusing `tetra_inner_eq`; water's H–O–H
  occupies two legs, the lone pairs the other two — the measured `104.5°` deviates from
  `arccos(−1/3) ≈ 109.47°` by lone-pair repulsion, a dynamical effect not formalized). The
  hydrogen-bond network closes into the `5¹²` clathrate cage: a trivalent polyhedron with pentagonal
  faces is *forced* by Euler's relation to be the pentagonal dodecahedron — `(V, E, F) = (20, 30, 12)`
  (`clathrate_cage_determined`): `20` water molecules, `30` hydrogen bonds, `12` pentagons, with
  rotation symmetry the icosahedral group of `IcosahedralStressEnergyAction`
  (`card_icosahedralGroup = 60`, `A5IcosahedralGroup`).

* **§D — the icosahedral stress and the surface-tension bridge.** The isotropic surface stress
  `σ·δ⊗δ` is invariant under *every* index permutation (`isotropicSurfaceStress_perm_invariant`),
  a fortiori under the clathrate's icosahedral group (`isotropicSurfaceStress_icosahedrally_invariant`),
  and is a fixed point of the icosahedral Reynolds average
  (`icosahedralAverage_isotropicSurfaceStress`): the cage symmetry supports exactly the isotropic
  macroscopic stress that enters the bubble momentum balance — the Einstein–Cartan fluid ledger of
  `WeylCartanFluidNoether` (`geometricForceDefect`, `corollary1_energyMomentum_conserved`) with zero
  geometric defect. Dimensionally the bridge is exact: bond energy per molecular area *is* a surface
  tension, `[E]/[A] = [σ]` (`surfaceTension_from_bondEnergy` — the `surfaceTension_dim` of
  `BubblePairLocalFrame`, closing the loop to `weberNumber`).

**Honest layering.** §A is exact arithmetic over the aufbau list and the SU(5)-generated quantum
numbers; §B is exact operator algebra on the `IsCAR` carrier (the identification of `f, g` with H `1s`
/ O `2p` orbitals is the LCAO modeling step; spin multiplicity is recorded, not formalized as a tensor
factor); §C is exact linear algebra and the Euler-relation determination (that water *adopts* sp³
geometry and forms `5¹²` cages is chemistry input); §D is exact tensor algebra and dimensional
analysis. Numerical bond energies, the `104.5°` angle, and hydrogen-bond strengths are empirical and
appear only in docstrings.

## References

* Aufbau/Madelung filling; octet rule — `Physlib` (`PeriodicTableAufbauStructure`).
* Georgi–Glashow SU(5) charge quantization — `Physlib` (`Su5StandardModelAnomalyFree`);
  colour-singlet baryon — `Physlib` (`ColorSingletBaryon`).
* LCAO/molecular-orbital theory; Bogoliubov transformations — `Physlib`
  (`Bogoliubov.CARAlgebraAutomorphism`, `AlgebraicQFT.ConfigurationSpaceDiracFluctuation` §C–§D).
* sp³ hybrids / SIC tetrahedral frame — `Physlib` (`TetrahedralLorentzFrame`); clathrate hydrate
  `5¹²` cages (Pauling); icosahedral Reynolds averaging — `Physlib`
  (`IcosahedralStressEnergyAction`, `A5IcosahedralGroup`).
* Zhang et al., bubble-pair interactions (the macroscopic side) — `Physlib`
  (`FluidDynamics.BubblePairLocalFrame`).


-/

set_option autoImplicit false

@[expose] public section

noncomputable section

namespace CondensedMatter.WaterCovalentBonding

open Physlib.QuantumMechanics.ComplexAction.PeriodicTableAufbauStructure
open Physlib.QuantumMechanics.ComplexAction.Su5StandardModelAnomalyFree
open Physlib.QuantumMechanics.ComplexAction.Bogoliubov.CARAlgebraAutomorphism
open Physlib.QuantumMechanics.ComplexAction.TetrahedralLorentzFrame
open Physlib.QuantumMechanics.ComplexAction.IcosahedralStressEnergyAction
open Physlib.Units.GravitationalCouplingDimensions
open Physlib.Units.InformationDimensionCollision
open Dimension


/-! ## §A — hydrogen and oxygen: aufbau valence and particle charges -/

/-- Hydrogen's atomic number. -/
def hydrogenZ : ℕ := 1

/-- Oxygen's atomic number. -/
def oxygenZ : ℕ := 8

/-- Carbon's atomic number. -/
def carbonZ : ℕ := 6

/-- **[Hydrogen is monovalent]** hydrogen sits one electron below the helium closure
`cumulativeCapacity 1 = 2`: one hole, one bond. -/
theorem hydrogen_monovalent : cumulativeCapacity 1 - hydrogenZ = 1 := by
  rw [noble_gas_numbers.1, hydrogenZ]

/-- **[Oxygen is divalent]** oxygen sits two electrons below the neon closure
`cumulativeCapacity 3 = 10`: two holes, two bonds — the two O–H bonds of water. -/
theorem oxygen_divalent : cumulativeCapacity 3 - oxygenZ = 2 := by
  rw [noble_gas_numbers.2.1, oxygenZ]

/-- **[Water stoichiometry is forced]** the number of hydrogens whose single electrons
(`hydrogenZ = 1` each) close oxygen's octet is *uniquely* `2`: H₂O is the only neutral saturated
hydride of oxygen. -/
theorem water_stoichiometry :
    ∃! n : ℕ, n * hydrogenZ = cumulativeCapacity 3 - oxygenZ := by
  rw [noble_gas_numbers.2.1]
  exact ⟨2, by norm_num [hydrogenZ, oxygenZ], fun m hm => by
    simp only [hydrogenZ, oxygenZ] at hm; omega⟩

/-- **[Methane stoichiometry is forced]** for carbon the same octet count gives *uniquely* `4` — the
CH₄ of `TetrahedralNuclearSpinWeights`, whose four bonds realize the §C tetrahedral legs. -/
theorem methane_stoichiometry :
    ∃! n : ℕ, n * hydrogenZ = cumulativeCapacity 3 - carbonZ := by
  rw [noble_gas_numbers.2.1]
  exact ⟨4, by norm_num [hydrogenZ, carbonZ], fun m hm => by
    simp only [hydrogenZ, carbonZ] at hm; omega⟩

/-- **[The proton charge is `+1` by SU(5) quantization]** the hydrogen nucleus `uud` — a colour
singlet (`ColorSingletBaryon`) — has electric charge `2/3 + 2/3 − 1/3 = 1` from the SU(5)-generated
quantum numbers, in every colour assignment. -/
theorem proton_charge_quantized (c₁ c₂ c₃ : QCDColour) :
    (threeGenerationQuantumNumbers (upQuarkParticle c₁)).electricCharge
      + (threeGenerationQuantumNumbers (upQuarkParticle c₂)).electricCharge
      + (threeGenerationQuantumNumbers (downQuarkParticle c₃)).electricCharge = 1 := by
  rw [(upQuarkParticle_hasQuantumNumbers c₁).1, (upQuarkParticle_hasQuantumNumbers c₂).1,
    (downQuarkParticle_hasQuantumNumbers c₃).1]
  norm_num

/-- **[The proton has unit baryon number]** `1/3 + 1/3 + 1/3 = 1`. -/
theorem proton_baryon_one (c₁ c₂ c₃ : QCDColour) :
    (threeGenerationQuantumNumbers (upQuarkParticle c₁)).baryonNumber
      + (threeGenerationQuantumNumbers (upQuarkParticle c₂)).baryonNumber
      + (threeGenerationQuantumNumbers (downQuarkParticle c₃)).baryonNumber = 1 := by
  rw [(upQuarkParticle_hasQuantumNumbers c₁).2.2.2.1,
    (upQuarkParticle_hasQuantumNumbers c₂).2.2.2.1,
    (downQuarkParticle_hasQuantumNumbers c₃).2.2.2.1]
  norm_num

/-- **[The hydrogen atom is exactly neutral]** proton (`uud`) plus electron: the SU(5) charges
cancel to zero — the quantization that lets atoms bind into neutral molecules. -/
theorem hydrogen_neutral (c₁ c₂ c₃ : QCDColour) :
    (threeGenerationQuantumNumbers (upQuarkParticle c₁)).electricCharge
      + (threeGenerationQuantumNumbers (upQuarkParticle c₂)).electricCharge
      + (threeGenerationQuantumNumbers (downQuarkParticle c₃)).electricCharge
      + (threeGenerationQuantumNumbers electronParticle).electricCharge = 0 := by
  rw [proton_charge_quantized c₁ c₂ c₃, electronParticle_hasQuantumNumbers.1]
  norm_num

/-- **[Every atom is exactly neutral]** `Z` protons and `Z` electrons: `Z·(+1) + Z·(−1) = 0` —
hydrogen at `Z = 1`, oxygen at `Z = 8`. -/
theorem atom_neutral (Z : ℕ) (c₁ c₂ c₃ : QCDColour) :
    (Z : ℚ) * ((threeGenerationQuantumNumbers (upQuarkParticle c₁)).electricCharge
        + (threeGenerationQuantumNumbers (upQuarkParticle c₂)).electricCharge
        + (threeGenerationQuantumNumbers (downQuarkParticle c₃)).electricCharge)
      + (Z : ℚ) * (threeGenerationQuantumNumbers electronParticle).electricCharge = 0 := by
  rw [proton_charge_quantized c₁ c₂ c₃, electronParticle_hasQuantumNumbers.1]
  ring


/-! ## §B — the covalent bond in second quantization -/

section SecondQuantization

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
  {A : Type*} [Ring A] [StarRing A] [Module ℂ A]

/-- **The bonding orbital** `(f + g)/√2` — the symmetric LCAO combination of the two atomic
orbitals (H `1s` and O `2p` in water's O–H bond). -/
def bondingOrbital (f g : K) : K := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • (f + g)

/-- **The antibonding orbital** `(f − g)/√2` — the antisymmetric LCAO combination. -/
def antibondingOrbital (f g : K) : K := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • (f - g)

/-- The normalization scalar is real: conjugation fixes `(√2)⁻¹`. -/
private lemma conj_invSqrtTwo :
    (starRingEnd ℂ) (((Real.sqrt 2 : ℝ) : ℂ)⁻¹) = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ := by
  rw [map_inv₀, Complex.conj_ofReal]

/-- The normalization squares to one half: `(√2)⁻¹·(√2)⁻¹ = 2⁻¹`. -/
private lemma invSqrtTwo_mul_self :
    ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = (2 : ℂ)⁻¹ := by
  rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
  norm_num

/-- **[The bonding orbital is normalized]** for orthonormal atomic orbitals,
`⟪(f+g)/√2, (f+g)/√2⟫ = 1`. -/
theorem bondingOrbital_normalized (f g : K) (hf : inner ℂ f f = 1) (hg : inner ℂ g g = 1)
    (hfg : inner ℂ f g = 0) (hgf : inner ℂ g f = 0) :
    inner ℂ (bondingOrbital f g) (bondingOrbital f g) = 1 := by
  simp only [bondingOrbital, inner_smul_left, inner_smul_right, inner_add_left, inner_add_right,
    hf, hg, hfg, hgf, conj_invSqrtTwo]
  linear_combination 2 * invSqrtTwo_mul_self

/-- **[The antibonding orbital is normalized]** `⟪(f−g)/√2, (f−g)/√2⟫ = 1`. -/
theorem antibondingOrbital_normalized (f g : K) (hf : inner ℂ f f = 1) (hg : inner ℂ g g = 1)
    (hfg : inner ℂ f g = 0) (hgf : inner ℂ g f = 0) :
    inner ℂ (antibondingOrbital f g) (antibondingOrbital f g) = 1 := by
  simp only [antibondingOrbital, inner_smul_left, inner_smul_right, inner_sub_left,
    inner_sub_right, hf, hg, hfg, hgf, conj_invSqrtTwo]
  linear_combination 2 * invSqrtTwo_mul_self

/-- **[Bonding ⊥ antibonding]** the LCAO rotation is orthogonal: `⟪(f+g)/√2, (f−g)/√2⟫ = 0`. -/
theorem bonding_antibonding_orthogonal (f g : K) (hf : inner ℂ f f = 1)
    (hg : inner ℂ g g = 1) (hfg : inner ℂ f g = 0) (hgf : inner ℂ g f = 0) :
    inner ℂ (bondingOrbital f g) (antibondingOrbital f g) = 0 := by
  simp only [bondingOrbital, antibondingOrbital, inner_smul_left, inner_smul_right,
    inner_add_left, inner_sub_right, hf, hg, hfg, hgf, conj_invSqrtTwo]
  ring

/-- **[The bonding mode satisfies the CAR]** `{B(bond), B(bond)†} = 1`: the covalent-bond mode is a
canonical fermion mode — the two-mode instance of the Bogoliubov automorphism
(`bogoliubov_preserves_CAR`, dead-wood `basisChange_CAR_kernel`/`seaMode`). -/
theorem bondingMode_CAR (B : K → A) (hB : IsCAR B) (f g : K) (hf : inner ℂ f f = 1)
    (hg : inner ℂ g g = 1) (hfg : inner ℂ f g = 0) (hgf : inner ℂ g f = 0) :
    B (bondingOrbital f g) * star (B (bondingOrbital f g))
      + star (B (bondingOrbital f g)) * B (bondingOrbital f g) = 1 := by
  rw [hB.1, bondingOrbital_normalized f g hf hg hfg hgf, one_smul]

/-- **[Bonding and antibonding modes are independent fermions]** `{B(bond), B(antibond)†} = 0`. -/
theorem bonding_antibonding_CAR (B : K → A) (hB : IsCAR B) (f g : K) (hf : inner ℂ f f = 1)
    (hg : inner ℂ g g = 1) (hfg : inner ℂ f g = 0) (hgf : inner ℂ g f = 0) :
    B (bondingOrbital f g) * star (B (antibondingOrbital f g))
      + star (B (antibondingOrbital f g)) * B (bondingOrbital f g) = 0 := by
  rw [hB.1, bonding_antibonding_orthogonal f g hf hg hfg hgf, zero_smul]

/-- **[Pauli exclusion on the bond]** `B(bond)² = 0`: at most one electron per spin channel occupies
the bonding orbital — the covalent bond is a *shared pair* (one spin-up, one spin-down), no more. -/
theorem bondingMode_pauli (B : K → A) (hB : IsCAR B) (f g : K) :
    B (bondingOrbital f g) * B (bondingOrbital f g) = 0 := by
  have h2 : (2 : ℂ) • (B (bondingOrbital f g) * B (bondingOrbital f g)) = 0 := by
    rw [two_smul]
    exact hB.2 _ _
  have hscaled := congrArg (fun z => ((2 : ℂ)⁻¹) • z) h2
  simpa [smul_smul] using hscaled

/-- **[The LCAO Hamiltonian diagonalizes in the bond basis]** as an exact operator identity:
`ε(a†a + b†b) − t(a†b + b†a) = (ε−t)·p†p + (ε+t)·m†m` with `p = (a+b)/√2`, `m = (a−b)/√2` (here in
quadratic-form shape with the `1/2` made explicit). The bonding level lies *lower by `2t`* — the
covalent bond energy that §D converts into a surface tension. -/
theorem lcao_diagonalization {A : Type*} [Ring A] [StarRing A] [Module ℂ A]
    [SMulCommClass ℂ A A] [IsScalarTower ℂ A A] (eps t : ℂ) (a b : A) :
    (eps - t) • ((2 : ℂ)⁻¹ • ((star a + star b) * (a + b)))
      + (eps + t) • ((2 : ℂ)⁻¹ • ((star a - star b) * (a - b)))
      = eps • (star a * a + star b * b) - t • (star a * b + star b * a) := by
  simp only [mul_add, add_mul, sub_mul, mul_sub, smul_add, smul_sub, smul_smul]
  module

end SecondQuantization


/-! ## §C — sp³ geometry and the clathrate cage -/

/-- **[The sp³ bond angle]** the cosine of the angle between two distinct tetrahedral legs is
`⟪vᵢ,vⱼ⟫/⟪vᵢ,vᵢ⟫ = −1/3` — water's two O–H bonds (and two lone pairs) point along four such legs;
`arccos(−1/3) ≈ 109.47°` is the ideal angle (the measured `104.5°` deviation is lone-pair
repulsion, not formalized). Reuses the SIC/tight-frame Gram matrix `tetra_inner_eq`. -/
theorem sp3_bond_angle_cos (i j : Fin 4) (hij : i ≠ j) :
    tetraInner i j / tetraInner i i = -(1 / 3) := by
  rw [tetra_inner_eq, tetra_inner_eq, if_neg hij, if_pos rfl]
  norm_num

/-- **[Euler's relation forces the `5¹²` clathrate cage]** a trivalent polyhedron (`3V = 2E` — three
hydrogen bonds per water vertex) with pentagonal faces (`5F = 2E`) must have
`(V, E, F) = (20, 30, 12)`: the pentagonal dodecahedron — `20` water molecules, `30` hydrogen
bonds, `12` pentagons, the `(H₂O)₂₀` clathrate cage with icosahedral rotation symmetry
(`card_icosahedralGroup = 60`). -/
theorem clathrate_cage_determined (V E F : ℤ) (h3 : 3 * V = 2 * E) (h5 : 5 * F = 2 * E)
    (hEuler : V - E + F = 2) : V = 20 ∧ E = 30 ∧ F = 12 := by
  omega


/-! ## §D — the icosahedral surface stress and the bridge to the bubble medium -/

section IcosahedralStress

variable {ι : Type*} [DecidableEq ι]

open Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor in
/-- **The isotropic surface stress** `σ·δ_{ac}δ_{bd}` — the pure surface-tension form of the stress
tensor, scalar `σ` times the identity pairing. -/
def isotropicSurfaceStress (sigma : ℝ) :
    Physlib.QuantumMechanics.ComplexAction.Curvature.RiemannCurvatureTensor.RiemannTensor ι :=
  fun a b c d => sigma * ((if a = c then (1 : ℝ) else 0) * (if b = d then 1 else 0))

/-- **[Isotropy is full permutation invariance]** the isotropic stress is fixed by *every* index
permutation — Kronecker deltas see only equality of indices. -/
theorem isotropicSurfaceStress_perm_invariant (sigma : ℝ) (σ : Equiv.Perm ι) :
    tensorPerm σ (isotropicSurfaceStress sigma) = isotropicSurfaceStress (ι := ι) sigma := by
  funext a b c d
  simp [tensorPerm, isotropicSurfaceStress, EmbeddingLike.apply_eq_iff_eq]

/-- **[The clathrate symmetry supports the isotropic stress]** the isotropic surface stress is
icosahedrally invariant for every action of the cage's rotation group. -/
theorem isotropicSurfaceStress_icosahedrally_invariant (sigma : ℝ) [Fintype ι]
    (ρ : IcosahedralGroup →* Equiv.Perm ι) :
    IcosahedrallyInvariant ρ (isotropicSurfaceStress sigma) := fun γ =>
  isotropicSurfaceStress_perm_invariant sigma (ρ γ)

/-- **[The isotropic stress is a fixed point of the icosahedral Reynolds average]**
`⟨σ·δ⊗δ⟩ = σ·δ⊗δ`: averaging the microscopic cage stress over the icosahedral group returns it
unchanged — the macroscopic surface stress of the water medium is exactly the isotropic one that
enters the bubble momentum balance and the Weber number of `BubblePairLocalFrame`. -/
theorem icosahedralAverage_isotropicSurfaceStress (sigma : ℝ) [Fintype ι]
    (ρ : IcosahedralGroup →* Equiv.Perm ι) :
    icosahedralAverage ρ (isotropicSurfaceStress sigma) = isotropicSurfaceStress sigma := by
  unfold icosahedralAverage
  rw [Finset.sum_congr rfl fun γ _ => isotropicSurfaceStress_perm_invariant sigma (ρ γ),
    Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    inv_mul_cancel₀ (by rw [card_icosahedralGroup]; norm_num), one_smul]

end IcosahedralStress

set_option backward.isDefEq.respectTransparency false in
/-- **[Bond energy per molecular area is a surface tension]** `[E]/[A] = [σ]` in the dimension
group: the microscopic hydrogen-bond energy divided by the area a molecule occupies at the interface
carries exactly the `surfaceTension_dim` of `BubblePairLocalFrame` — the dimensional bridge from the
§B covalent bond to the macroscopic `weberNumber` of the bubble pair. -/
theorem surfaceTension_from_bondEnergy :
    energy_dim / area_dim = FluidDynamics.BubblePairLocalFrame.surfaceTension_dim := by
  ext b <;> cases b <;>
    norm_num [energy_dim, area_dim, FluidDynamics.BubblePairLocalFrame.surfaceTension_dim]

end CondensedMatter.WaterCovalentBonding

end

end

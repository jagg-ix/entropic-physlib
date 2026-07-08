/-
Copyright (c) 2026 Jorge A. Garcia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jorge A. Garcia
-/
module

-- Information geometry / probability metrics
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.CramerDistanceCDFMetric
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.ProbabilityMetricInformationGeometry
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.ProbabilityMetricTranslationKillingFlow
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.SymmetricStableProcessMetricEntropy

-- Entropic-dynamics probability flow → free energy → equilibrium
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsLocalTimeFokkerPlanck
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWassersteinGradientFlow
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsFreeEnergyRelativeEntropy
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.GibbsEquilibriumComplexReversibility

-- Hamilton–Killing → quantum mechanics (wave function, Born rule, Schrödinger, Kähler)
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.EntropicDynamicsWaveFunctionReconstruction
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.HamiltonKillingNormalizationInformationMetric
public import Physlib.QuantumMechanics.ComplexAction.EntropicTime.HamiltonKillingComplexStructureSchrodinger

-- Compton clock / de Broglie / Nagao–Nielsen contour
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.FrequencyTrinity
public import Physlib.QuantumMechanics.ComplexAction.ComptonClock.NagaoNielsenMassShellCone
public import Physlib.QuantumMechanics.ComplexAction.HorizonCell.ElectronMadelungDeBroglieMomentum

-- Reversibility / arrow of time
public import Physlib.QuantumMechanics.Lindblad.ThreeClockReversibilitySpectrum

-- QM → GR: complex Einstein, curvature, second Bianchi
public import Physlib.QuantumMechanics.ComplexAction.ComplexEinstein.ComplexMassEinsteinEquations
public import Physlib.QuantumMechanics.ComplexAction.Curvature.SecondBianchiCyclicFamily

-- Holography / AdS-CFT
public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.ConformalBoundaryRepoLinks
public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.JohnsonLindenstraussHolographicReduction
public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.JohnsonLindenstraussLipschitzExtension
public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.JohnsonLindenstraussEpsilonNetPacking
public import Physlib.QuantumMechanics.ComplexAction.AdSCFT.RyuTakayanagiHolographicEntropy
public import Physlib.Mathematics.Geometry.StereographicRiemannSphere

-- Double copy / Maxwell
public import Physlib.QuantumMechanics.ComplexAction.BCJDoubleCopy.ColorKinematicsDoubleCopy
public import Physlib.QuantumMechanics.ComplexAction.PTSymmetricQFT.MaxwellFaraday
public import Physlib.QuantumMechanics.ComplexAction.Electromagnetic.MaxwellContinuityCovariant

-- Thermodynamics of computation / H-theorem
public import Physlib.Thermodynamics.SecondLawQuantumBoltzmann
public import Physlib.Thermodynamics.ComputationLandauer

-- Information dimension [I] + scalar-action no-go
public import Physlib.Units.Dimension
public import Physlib.Units.ComplexActionDimension

/-!
# The entropic-dynamics QM→GR spine (real modules)

A curated aggregator of the formalizations that constitute the entropic-dynamics
Quantum-Mechanics-to-General-Relativity spine. Every module imported above is a real
formalization in this repository, with this file serving as the review entry point.

## Source and equation map

This aggregator is organized around the following source-backed equation families.
The details live in the imported modules; this file records the provenance at the PR
boundary so reviewers can see what the spine is meant to expose.

### Relative entropy and entropic proper time

* H. Umegaki, *Conditional expectation in an operator algebra. IV. Entropy and
  information*, Kodai Mathematical Seminar Reports 14 (1962), 59-85,
  doi:10.2996/kmj/1138844604: finite relative entropy
  `D(ρ‖σ) = Tr(ρ(log ρ - log σ))`.
* H. Araki, *Relative Entropy of States of von Neumann Algebras*, Publications of the
  Research Institute for Mathematical Sciences 11 (1976), 809-833,
  doi:10.2977/prims/1195191148: modular relative entropy and the faithful finite
  specialization used by `QuantumInfo.Finite.entropicProperTime`.
* A. Connes and C. Rovelli, *Von Neumann algebra automorphisms and
  time-thermodynamics relation in generally covariant quantum theories*, Classical and
  Quantum Gravity 11 (1994), 2899-2918, doi:10.1088/0264-9381/11/12/007: thermal-time
  motivation. The branch does not identify `τ_ent` with modular flow; it uses the
  finite scalar `D(ρ‖σ)` and the metric lift below.

Formal spine equations:

* `τ_ent(ρ,σ) = D(ρ‖σ)`;
* `τ_ent,metric = (ℏ/(k_B T_∞)) D(ρ‖σ)`;
* `τ_total = τ_geom + (ℏ/(k_B T_∞)) D(ρ‖σ)`;
* frozen limit `ρ = σ`: `τ_total = τ_geom`.

### Lapse, Tolman scaling, and thermal time

* R. C. Tolman, *On the Weight of Heat and Thermal Equilibrium in General
  Relativity*, Physical Review 35 (1930), 904-924, doi:10.1103/PhysRev.35.904.
* R. C. Tolman and P. Ehrenfest, *Temperature Equilibrium in a Static Gravitational
  Field*, Physical Review 36 (1930), 1791-1798, doi:10.1103/PhysRev.36.1791.
* C. Rovelli and M. Smerlak, *Thermal time and Tolman-Ehrenfest effect: temperature
  as the speed of time*, Classical and Quantum Gravity 28 (2011), 075007,
  doi:10.1088/0264-9381/28/7/075007.

Formal spine equations:

* positive lapse `N : SpaceTime d → ℝ`, `0 < N x`;
* Tolman invariant `O_loc(x) * N(x) = O_∞`;
* entropic-time local law `τ_ent,loc(x) * N(x) = τ_ent,∞`.

### Entropic dynamics, Fokker-Planck flow, and quantum mechanics

* S. Ipek, M. Abedi, and A. Caticha, *Reconstructing Quantum Field Theory in
  Curved Space-time*, arXiv:1803.07493: transition probability, local-time
  Fokker-Planck equation, and canonical entropic dynamics. Imported modules cite
  Eq. 6 (`P(Δχ) ∝ exp(-α(Δχ-b)^2/2)`), Eq. 8 (drift), Eq. 9 (fluctuation
  variance), Eq. 13 (local duration), Eq. 16 (local-time Fokker-Planck current),
  Eq. 20 (ensemble Hamiltonian), Eq. 38 (constraint split), and Eqs. 66-67
  (ensemble Hamiltonian and quantum potential).
* A. Caticha, *Entropic Dynamics: Quantum Mechanics from Entropy and Information
  Geometry*, arXiv:2107.08502: Hamiltonian/Killing flow on the statistical
  manifold, Fisher-Rao metric, Kähler complex structure, Born coordinates, and the
  linear Schrödinger equation. Imported modules cite Eqs. 7, 9, 15-18, 20, 24, 26,
  30, 32, 35, 39, 45, 48-49.
* R. Jordan, D. Kinderlehrer, and F. Otto, *The Variational Formulation of the
  Fokker-Planck Equation*, SIAM Journal on Mathematical Analysis 29 (1998), 1-17,
  doi:10.1137/S0036141096303359: Wasserstein gradient flow and free-energy
  Lyapunov functional.

Formal spine equations include the current potential `Φ = φ - (1/2) log ρ`, the
local-time Fokker-Planck current `δρ/δξ⊥ = -(1/√g) ∂χ(ρ ∂χΦ)`, the Gibbs/free-energy
identity `F(ρ)-F(ρ_s)=β⁻¹ D_KL(ρ‖ρ_s)`, the Fisher metric, the complex structure
`J^2 = -1`, the wave function `ψ = √ρ exp(iΦ)`, and `i dψ/dτ = Hψ`.

### Path integrals, complex action, and damping

* R. P. Feynman, *Space-Time Approach to Non-Relativistic Quantum Mechanics*,
  Reviews of Modern Physics 20 (1948), 367-387, doi:10.1103/RevModPhys.20.367.
* M. Kac, *On Distributions of Certain Wiener Functionals*, Transactions of the
  American Mathematical Society 65 (1949), 1-13, doi:10.2307/1990512.
* H. B. Nielsen and M. Ninomiya, complex-action programme; and K. Nagao with
  H. B. Nielsen, arXiv:1902.01424, for the complex-action oscillator/mass-shell
  contour material used by the imported complex-action modules.

Formal spine equations include `exp(iS/ℏ) = exp(iS_R/ℏ - S_I/ℏ)` when
`S = S_R + i S_I`, the damping bound for `S_I ≥ 0`, Feynman-Kac weights, and the
complex-action mass-shell/contour bridges imported above.

### Quantum thermodynamics, horizons, and holography

* L. Brillouin, *Science and Information Theory* (1956), and R. Landauer,
  *Irreversibility and Heat Generation in the Computing Process*, IBM Journal of
  Research and Development 5 (1961), 183-191, doi:10.1147/rd.53.0183: information
  cost and the information-dimension bookkeeping used by the units layer.
* S. W. Hawking, *Particle Creation by Black Holes*, Communications in Mathematical
  Physics 43 (1975), 199-220, doi:10.1007/BF02345020; W. G. Unruh, *Notes on
  black-hole evaporation*, Physical Review D 14 (1976), 870-892,
  doi:10.1103/PhysRevD.14.870; T. Jacobson, *Thermodynamics of Spacetime: The
  Einstein Equation of State*, Physical Review Letters 75 (1995), 1260-1263,
  doi:10.1103/PhysRevLett.75.1260.
* S. Ryu and T. Takayanagi, *Holographic Derivation of Entanglement Entropy from
  AdS/CFT*, Physical Review Letters 96 (2006), 181602,
  doi:10.1103/PhysRevLett.96.181602: `S_A = Area(γ_A)/(4G_N)`.

Formal spine equations include Landauer bounds, second-law/quantum-Boltzmann
entropy production, Hawking/Unruh/Jacobson thermal-gravity interfaces, and the
Ryu-Takayanagi area law imported by the AdS/CFT modules.

### Geometry, embeddings, and double-copy interfaces

* W. B. Johnson and J. Lindenstrauss, *Extensions of Lipschitz mappings into a
  Hilbert space*, Contemporary Mathematics 26 (1984), 189-206,
  doi:10.1090/conm/026/737400: dimension-reduction and Lipschitz-extension
  structure used by the holographic-reduction modules.
* Z. Bern, J. J. M. Carrasco, and H. Johansson, *New Relations for Gauge-Theory
  Amplitudes*, Physical Review D 78 (2008), 085011, doi:10.1103/PhysRevD.78.085011:
  color-kinematics/BCJ double-copy structure used by the imported gauge-gravity
  bridge modules.

No new axioms are introduced by this aggregator; it only re-exports the source-backed
modules listed above.
-/

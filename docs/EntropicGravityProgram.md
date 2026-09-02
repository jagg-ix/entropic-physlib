# The Entropic-Gravity Program: A Reader's Guide

## The idea

Most physical theories treat gravity as fundamental. There is an old and serious suspicion
that it is not — that gravity is a statistical effect, the way pressure is: a gas has no
"pressure force" at the level of individual molecules, yet pressure emerges reliably from
counting them. In 2011 Erik Verlinde made this concrete: he showed that if you assume
information about matter is stored on surfaces ("holographic screens"), and that this
information carries entropy and temperature, then Newton's law of gravitation *falls out* of
thermodynamics.

The catch: Verlinde's argument rests on several postulates he had to write down by hand —
a formula for how much entropy a moving mass generates, a temperature for the screen, a rule
for how many information bits a screen holds. Critics have argued about these assumptions
ever since, largely in prose.

This repository develops that proposal as a machine-checked network of thermodynamic,
information-theoretic, quantum, and geometric results. It contains direct constructions,
existence-and-uniqueness results, equivalences, variational results, and experimentally
anchored interfaces. Lean checks every stated conclusion from the hypotheses written in its
declaration; the ZIL graph separately records how the physical claims, evidence, and derived
premises connect. The scientific content is therefore the complete network of proved
interfaces, including the routes that derive or discharge inputs used by other routes.

## How to read the theorems

The repository uses several logical forms, and they should not be collapsed into one. A
definition constructs an object; a direct lemma proves a property of that object; an
existence-and-uniqueness result proves that exactly one object satisfies a specification;
and an **"if and only if"** result proves that two formulations determine each other. A
representative equivalence says:

> *Assume* forces arise from entropy differences at a temperature (the entropic-force rule),
> and *assume* an accelerating observer sees the temperature Unruh predicted. *Then*
> Verlinde's entropy formula holds **exactly when** Newton's second law `F = ma` holds.

For that declaration, the entropic-force and Unruh interfaces are explicit parameters, and
the equivalence proves that the entropy law and inertial response are the same constraint.
Other declarations go further in different directions: they construct screen counts,
derive equipartition from a canonical ensemble, prove unique couplings, and propagate those
couplings through Newtonian, Einstein, horizon, and complex-action sectors. Each result must
be read through its own Lean signature and its transitive ZIL dependencies.

## The results

### 1. Thermodynamic interfaces and their derivation

Three quantities organize the thermodynamic route:

- **The entropic-force rule.** A force is what you get from an entropy change `ΔS` at
  temperature `T` across a displacement `Δx`: namely `F = T·ΔS/Δx`. This is the heart of the
  entropic picture — the analogue of "pressure comes from counting molecules."
- **The Unruh temperature.** The acceleration-temperature carrier is
  `T = ħa/(2πk_B c)`. The repository connects this carrier to the Hawking/KMS temperature
  and to its Compton and de Broglie welding conditions.
- **The screen temperature.** A screen storing `N` bits about a mass `M` is assigned
  temperature `T = 2Mc²/(N·k_B)` — energy shared equally among the bits. This
  classical equipartition relation is derived by `verlinde_equipartition_from_NDOF` from
  the canonical ensemble of `N` non-interacting quadratic degrees of freedom. Inverting
  it gives the thermodynamic count `screenBitCount E k_B T = 2E/(k_B T)`.

A first structural fact is proved right here: written through these rules, the force law
contains **no Newton's constant at all**. `G` only ever enters later, through the *number of
bits* assigned to a screen. That observation drives everything below.

*In the code:*
[`Physlib/Thermodynamics/VerlindeEntropicForce.lean`](../Physlib/Thermodynamics/VerlindeEntropicForce.lean),
[`VerlindeEquipartitionDerivation.lean`](../Physlib/Thermodynamics/VerlindeEquipartitionDerivation.lean),
[`NewtonGIsolation.lean`](../Physlib/Thermodynamics/NewtonGIsolation.lean), and
[`HolographicGravityFromModularFlow.lean`](../Physlib/QuantumMechanics/ComplexAction/HolographicGravityFromModularFlow.lean)
(`verlindeEntropicForce`, `unruhTemperature`, `bitScreenTemperature`,
`verlinde_equipartition_from_NDOF`, `screenBitCount`, `entropicForce_bitForm`,
`newtonG_isolated`).

### 2. Verlinde's entropy formula is not a free choice

Verlinde postulated that moving a mass `m` by a distance `Δx` changes a screen's entropy by
`ΔS = 2πk_B (mc/ħ)·Δx`. This looked like the most arbitrary step of his paper. The
repository proves it is not arbitrary at all:

> Given the entropic-force rule and the Unruh temperature, the entropic force reproduces
> `F = ma` at every acceleration **if and only if** the entropy formula is exactly
> Verlinde's.

So within the stated entropic and thermal interfaces, his postulate and Newton's second law
are equivalent — there is no alternative scalar entropy compatible with the response law.
The repository proves existence and uniqueness at nonzero acceleration, proves independence
from which nonzero acceleration is used, and separately characterizes the zero-acceleration
degeneracy. It also rewrites the result as `2π` nats per probe-mass Compton wavelength.

*In the code:*
[`DisplacementEntropyFromUnruhInertia.lean`](../Physlib/QuantumMechanics/ComplexAction/ComptonClock/DisplacementEntropyFromUnruhInertia.lean)
(`existsUnique_displacementEntropy`, `displacementEntropy_a_independent`,
`verlindeEntropy_iff_inertial_response_law`,
`not_existsUnique_displacementEntropy_at_zero_acceleration`, and
`displacementEntropy_eq_two_pi_nats_per_comptonCell`).

### 3. Building the screen out of quantum uncertainty

Where do the screen's "bits" come from? The construction here: a measurement screen that
localizes particles with Gaussian uncertainty of width `σ₀` has a natural information
density (in the Fisher-information sense — the statistician's measure of how much a
measurement can tell you). Tiling a spherical surface with cells of that density and applying
the rules of §1 yields a force with Newton's exact `1/R²` form, with coupling constant
`G = ħcσ₀⁴`.

This is a direct construction of the inverse-square response in the formalized screen
system. The screen count has two complementary `G`-free operational forms in the repository:
the thermodynamic count `N = 2E/(k_B T)` and the Compton-cell count `N = A/λ_C²`. The latter
cell scale is tied to the measured Compton scattering shift by
`comptonShift_right_angle`, `cellArea_eq_shift_sq`, and
`comptonBitDensity_eq_inv_shift_sq`. Given positive independently supplied area and cell
count, `GFreeComptonCellCalibration` constructs the screen mass, inference width, Planck
cell, and a unique coupling without taking `G` as input. The ZIL edges retain the precise
physical identification used by each branch instead of replacing the construction with a
blanket label.

*In the code:*
[`GaussianFisherGravitationalResponse.lean`](../Physlib/QuantumMechanics/ComplexAction/ComptonClock/GaussianFisherGravitationalResponse.lean),
[`ComptonCellNewtonConstant.lean`](../Physlib/QuantumMechanics/ComplexAction/ComptonClock/ComptonCellNewtonConstant.lean), and
[`DeBroglieDispersionComptonAnchor.lean`](../Physlib/QuantumMechanics/ComplexAction/ComptonClock/DeBroglieDispersionComptonAnchor.lean)
(`comptonBitDensity`, `tiledScreen_gravitationalResponse`, `operational_newtonG_eq_info`,
`GFreeComptonCellCalibration`, `existsUnique_countedNewtonG`,
`comptonShift_right_angle`, `cellArea_eq_shift_sq`,
`comptonBitDensity_eq_inv_shift_sq`).

### 4. Why the Planck scale appears

The matching between the constructed coupling `ħcσ₀⁴` and Newton's constant is characterized
exactly. The screen width is the Planck width, `σ₀ = (G/ħc)^{1/4}`, **if and only if**
the screen stores precisely one bit per Planck area. The width is unique: any other choice
gives a different response. In the independent-count branch, the same area per counted cell
constructs the Planck length, fixes the positive screen mass and inference width, and proves
`G_count = ħc/m_scr² = ħcσ₀⁴`.

*In the code:*
[`GaussianFisherPlanckCalibration.lean`](../Physlib/QuantumMechanics/ComplexAction/ComptonClock/GaussianFisherPlanckCalibration.lean)
(`identification_iff_planckDensity`, `existsUnique_calibration`).

### 5. Black-hole thermodynamic closure

Counting the §3 cells on a black-hole horizon gives exactly the Bekenstein–Hawking entropy
(area over four Planck areas), and the screen temperature of §1 evaluated at the horizon is
exactly Hawking's temperature. These theorems close the screen count, Bekenstein entropy,
Susskind holographic area law, Hawking temperature, and constructed coupling on the same
formal data.

*In the code:*
[`GaussianFisherHorizonConsistency.lean`](../Physlib/QuantumMechanics/ComplexAction/ComptonClock/GaussianFisherHorizonConsistency.lean)
(`tiled_horizonCount_eq_bekenstein`, `tiledScreen_at_horizon_is_hawking`).

### 6. The inverse-square law and holography determine each other

The deepest rigidity result. Suppose you knew nothing about how many bits screens hold — any
assignment of bit counts to spheres is on the table. Then, through the rules of §1:

> The force falls off exactly as `1/R²` **if and only if** the bit count is the holographic
> area law, and the coupling `G` it determines is unique.

Two companions sharpen this. First, among all power laws `N ∝ R^p`, only `p = 2` — area
scaling, the holographic choice — is compatible with inverse-square gravity: the exponent is
forced, not chosen. Second, the chain extends upward: the Newtonian limit forces the exact
normalization of Einstein's field equations (`κ = 8πG/c⁴`), and matching the screen coupling
in a string-theoretic (AdS/CFT) setting fixes the compactification volume uniquely.

There are two directions in the repository, and neither should be erased. The inverse
rigidity direction takes an arbitrary nowhere-zero screen profile and proves that exact
`1/R²` response forces the holographic area profile and its unique coupling. The constructive
direction starts from the Compton–Fisher density, proves that its count equals the
holographic count at `ħcσ₀⁴`, and then derives the `1/R²` response for every nonzero radius.
Thus the library contains both the uniqueness theorem and a concrete screen realization of
the law.

*In the code:*
[`UniqueInverseSquareHolographicCoupling.lean`](../Physlib/QuantumMechanics/ComplexAction/ComptonClock/UniqueInverseSquareHolographicCoupling.lean)
(`holographicProfile_iff_inverseSquare`, `powerLaw_bitScaling_inverseSquare_iff`,
`einsteinCoupling_unique_from_poisson`, `existsUnique_d3CompactificationVolume`,
`stack_from_inverseSquare`).

### 7. Measuring Newton's constant by counting

If `G` really is bookkeeping for a bit count, you should be able to determine it *without
ever measuring a gravitational force*: count the cells `N` on a screen of area `A`, and
compute `G = Ac³/(ħN)`. The repository proves this determination is unique, and closes the
triangle: the same counted data that fix `G` also predict the laboratory force of §3 at that
value. One constant, reachable three ways — by force measurement, by information count, by
screen construction — with theorems forcing all three to agree.

*In the code:*
[`ComptonCellNewtonConstant.lean`](../Physlib/QuantumMechanics/ComplexAction/ComptonClock/ComptonCellNewtonConstant.lean)
(`GFreeComptonCellCalibration`, `existsUnique_countedNewtonG`) and
`countedData_forces_response` in the §6 file.

### 8. Path integrals as information processing

A different route to the same conclusion. In the Feynman path-integral picture, environmental
friction suppresses quantum interference by a factor `exp(−ΔS/k_B)` (the Caldeira–Leggett
result). That exponent is an entropy — which means it is a *bit count*: suppression of a path
is the thermodynamic cost of the information erased along it, in Landauer's sense. Taking
this bookkeeping seriously forces an unusual conclusion: Newton's constant carries a unit of
information — dimensionally, `G` is (length³ / time² / mass / bit). The repository enforces
this with a dimensional type-checker: every equation in the program must balance in the
information dimension too, and does.

*In the code:*
[`PathIntegral/HolographicLandauerBridge.lean`](../Physlib/QuantumMechanics/ComplexAction/PathIntegral/HolographicLandauerBridge.lean)
and [`Physlib/Meta/PathIntegralBitGate.lean`](../Physlib/Meta/PathIntegralBitGate.lean)
(`kuikenWeight_entropicAction_eq_exp_natCount`, `areaPerBitCoupling`).

### 9. Complex action, entropic proper time, and Caticha's entropic dynamics

The gravitational construction is part of a wider dynamical picture in the repository.
Nagao and Nielsen replace a purely real action by a complex action

\[
S=S_R+iS_I.
\]

Its path-integral weight has the exact factorization

\[
e^{iS/\hbar}
  =e^{iS_R/\hbar}e^{-S_I/\hbar}.
\]

The two components have different dynamical roles. The real action supplies the oscillatory
phase, while the imaginary action supplies the positive or negative exponential selection of
histories. The repository proves the factorization, proves that the phase has unit modulus,
and proves

\[
\left\lVert e^{iS/\hbar}\right\rVert=e^{-S_I/\hbar},
\qquad
\tau_{\mathrm{ent}}
   :=\frac{S_I}{\hbar}
   =-\log\left\lVert e^{iS/\hbar}\right\rVert .
\]

This makes entropic proper time more than a label attached to an external clock. It is the
intrinsic accumulated imaginary action, equivalently the logarithmic ordering parameter of
the complex path weight. For positive `\hbar`, increasing `S_I` makes
`\tau_{\mathrm{ent}}` monotone and strengthens the suppression of a history; at `S_I=0`,
the entropic advance vanishes and the weight reduces to its reversible phase. When a concrete
dynamics supplies an action-production rate, the same quantity acquires physical time units.
For example, an action law

\[
\Delta S_I=\hbar\omega_0\,\Delta\tau
\]

gives `\Delta\tau_{\mathrm{ent}}=\omega_0\Delta\tau`, and division by the physical phase
frequency `\omega_0` recovers the elapsed proper time. The action-rate relation is therefore
the dimensional bridge from the intrinsic complex-action ordering variable to a clock
reading, rather than the definition of the ordering variable itself.

The repository also realizes entropic proper time directly on quantum states. For a pair of
states it defines the information-theoretic core as the quantum relative entropy
`D(\rho\Vert\sigma)`. The thermal scale converts this information interval into metric time,

\[
\tau_{\mathrm{ent}}^{\mathrm{metric}}
  =\frac{\hbar}{k_B T_\infty}D(\rho\Vert\sigma).
\]

The complex-action and information forms meet when the imaginary action is written as the
entropic action `S_I=(\hbar/k_B)S_{\mathrm{ent}}`; then
`S_I/\hbar=S_{\mathrm{ent}}/k_B`, and the modulus of the Nagao--Nielsen weight is the
Boltzmann-like information weight. Instantiating `S_{\mathrm{ent}}/k_B` with the
relative-entropy gap connects the state-space interval to the same damping exponent. Thus
relative entropy, imaginary action, and damping are three compatible representations once
the displayed conversion is supplied; the code keeps that conversion visible.

Caticha's entropic dynamics supplies the local transition and evolution side of this
correspondence. Its short-step field transition has the Gaussian weight

\[
P(\Delta\chi)\propto
  \exp\!\left[-\frac{\alpha}{2}(\Delta\chi-b)^2\right].
\]

Under the explicit identification

\[
S_I=(\Delta\chi-b)^2,
\qquad
\hbar_{\mathrm{eff}}=\frac{2}{\alpha},
\]

the repository proves that this transition weight is exactly the modulus
`e^{-S_I/\hbar_{\mathrm{eff}}}` of the complex-action weight. Caticha's current potential
supplies the other half: the reconstructed wave functional
`\Psi=\sqrt{\rho}\,e^{i\Phi}` has phase `\Phi=S_R/\hbar`. The transition modulus and wave
phase therefore reconstruct the imaginary and real parts of the same complex-action
integrand.

The identification also carries the local clock. Caticha's multiplier
`\alpha_x=1/\delta\xi_x^\perp` makes the fluctuation variance

\[
\left\langle\Delta w_x^2\right\rangle
  =\frac{\delta\xi_x^\perp}{\sqrt{g_x}},
\]

so local proper-time advance is measured by local diffusion. Substitution into the
complex-action map gives `\hbar_{\mathrm{eff}}=2\delta\xi_x^\perp`. The repository carries
this local clock through the Fokker--Planck continuity equation, its ensemble-Hamiltonian
generation, and the functional Schrödinger construction. In the coupled Ipek--Caticha
sector, the fixed-background generator is complex-linear, while the gravitational
backreaction is the nonlinear departure from that linear Schrödinger flow.

These links use the repository's additional **information dimension** `[I]`. Ordinary
dimensional analysis treats a bit or nat as just another dimensionless number. The extended
basis

\[
[L,T,M,C,\Theta,I]
\]

instead records information as an independent coordinate. In this convention `k_B` has
dimension `E\Theta^{-1}I^{-1}`: it converts an information count into thermodynamic entropy,
and `\hbar/(k_BT)` carries `T I`. Forgetting `[I]` maps the extended system back to ordinary
dimensional analysis, but the repository proves that this map is not injective; quantities
that differ only by information content become indistinguishable.

The code keeps two readings of complex action separate. In the standard scalar
Nagao--Nielsen reading, both `S_R` and `S_I` have the mechanical dimension of action, as
required for `e^{iS/\hbar}`. The repository then adds an information-graded reading in which
the imaginary sector has a nonzero `[I]` coordinate. That extra grading is not attributed to
Nagao and Nielsen; it is a repository extension that records the information carried by
irreversible selection. The same `[I]` axis types the holographic bit count as information
and Newton's constant as area per bit. It therefore joins the screen-counting, Landauer,
complex-action, and entropic-time sectors without erasing the conversion constants that move
between them.

*In the code:*
[`EntropicDampingEquivalence.lean`](../Physlib/QuantumMechanics/ComplexAction/NonHermitianComplexAction/EntropicDampingEquivalence.lean),
[`ComplexActionDampingCoercivity.lean`](../Physlib/QuantumMechanics/ComplexAction/PathIntegral/ComplexActionDampingCoercivity.lean),
and [`ComplexActionPathIntegralWeight.lean`](../Physlib/QuantumMechanics/ComplexAction/PathIntegral/ComplexActionPathIntegralWeight.lean)
for the complex-action factorization and entropic proper time
(`norm_nnPathWeight`, `entropicProperTime_eq_neg_log_norm`,
`master_modulus_is_entropy`);
[`EntropicDynamicsComplexActionNagaoNielsen.lean`](../Physlib/QuantumMechanics/ComplexAction/EntropicTime/EntropicDynamicsComplexActionNagaoNielsen.lean),
[`IpekCatichaTransitionLocalEntropicTime.lean`](../Physlib/QuantumMechanics/ComplexAction/EntropicTime/IpekCatichaTransitionLocalEntropicTime.lean),
and [`IpekCatichaSchrodingerNagaoNielsen.lean`](../Physlib/QuantumMechanics/ComplexAction/EntropicTime/IpekCatichaSchrodingerNagaoNielsen.lean)
for the Caticha--Nagao--Nielsen bridge (`ed_is_nagaoNielsen_complexAction`,
`local_clock_variance`, `ipekCaticha_on_nagaoNielsen_contour`);
[`EntropicDynamicsFokkerPlanckHamiltonian.lean`](../Physlib/QuantumMechanics/ComplexAction/EntropicTime/EntropicDynamicsFokkerPlanckHamiltonian.lean)
and [`IpekCatichaFunctionalSchrodinger.lean`](../Physlib/QuantumMechanics/ComplexAction/EntropicTime/IpekCatichaFunctionalSchrodinger.lean)
for the dynamical evolution;
[`EntropicProperTime.lean`](../Physlib/SpaceAndTime/EntropicProperTime.lean) and
[`ClockRelativeEntropy.lean`](../Physlib/QuantumMechanics/ComplexAction/EntropicTime/ClockRelativeEntropy.lean)
for the relative-entropy metric lift; and
[`LTMCTIDimensionBase.lean`](../Physlib/Units/LTMCTIDimensionBase.lean),
[`EntropicDimension.lean`](../Physlib/QuantumMechanics/ComplexAction/EntropicTime/EntropicDimension.lean),
[`ComplexActionDimension.lean`](../Physlib/Units/ComplexActionDimension.lean), and
[`GravitationalCouplingDimensions.lean`](../Physlib/Units/GravitationalCouplingDimensions.lean)
for the `[I]`-extended dimensional system (`forgetInfo_not_injective`,
`planckianPeriod_dim_framework_eq_null_mul_I`, `complexAction_ne_angularMomentum`,
`information_typing_unique`).

### 10. Where experiment enters

The repository formalizes an experimental interface for accelerated thermality. A detector
of mass `m` accelerating at `a` reaches the welding point when the Unruh temperature equals
its Compton temperature; the same module expresses the suppression scale as the ratio of
those temperatures. This is the regime targeted by a 2025 proposal to simulate a low-mass
detector in a superconducting qubit (arXiv:2512.17959), giving the formal temperature and
threshold relations a concrete measurement context.

*In the code:*
[`Physlib/Thermodynamics/UnruhDetectionThreshold.lean`](../Physlib/Thermodynamics/UnruhDetectionThreshold.lean)
(`suppressionScale_eq_temperatureRatio`, `detectionThreshold_iff_temperatures_weld`).

## How the scope of a claim is certified

No short prose list can replace the repository's dependency structure. Scope is certified
at three connected levels:

1. **Lean declaration.** The parameters and hypotheses in a declaration are the exact local
   interface from which its conclusion is proved.
2. **Constructive and converse routes.** A hypothesis in one theorem may be the output of a
   different construction. For example, classical equipartition is derived from the
   canonical ensemble; the Compton–Fisher branch constructs a holographic count and
   inverse-square response; and the inverse-rigidity branch proves uniqueness in the
   converse direction.
3. **ZIL transitive graph.** `formalizes`, `requires`, `derives`, `supported_by`, alias, and
   caveat edges record the claim-level provenance. A premise discharged elsewhere in the
   graph is not to be presented as an irreducible postulate merely because one theorem
   receives it through its interface.

Accordingly, this guide reports the positive content of the named theorem chains and
delegates dependency status to the generated graph. Claims about the physical interpretation
should cite the exact Lean route and its current transitive ZIL closure.

## Check it yourself

```bash
lake build                      # the whole library; no `sorry`, no `axiom` declarations
./scripts/zil-graph-report.sh   # regenerate the audit report: analysis/zil-graph-report.md
```

The program's annotated claims carry machine-readable metadata naming their dependencies and
support. The generated [`ZIL graph report`](../analysis/zil-graph-report.md) sweeps the full
graph and reports, among other things, primitive premises, derived-premise aliases, evidence
reach, and any exact claim that silently rests on a weaker one. The audit engine itself is
proved correct against its reference semantics
([`Physlib/Meta/ZilDatalogFastEquiv.lean`](../Physlib/Meta/ZilDatalogFastEquiv.lean),
`deriveProgramFast_eq`), so trusting the report does not require trusting a script.

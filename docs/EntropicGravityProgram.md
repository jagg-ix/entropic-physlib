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

This repository moves that argument into a proof assistant. Every step of the program is
formalized in Lean 4, which forces total explicitness: each theorem states *exactly* which
assumptions it uses, and a machine checks that nothing is smuggled in. The result is not a
proof that gravity is entropic. It is something more modest and more precise: a complete
account of **which assumptions buy which laws, which of Verlinde's postulates are actually
forced by the others, and what an experiment would have to measure to test the picture.**

## How to read the theorems

Almost every headline result here is an **"if and only if"** — an equivalence. A typical
example, in words:

> *Assume* forces arise from entropy differences at a temperature (the entropic-force rule),
> and *assume* an accelerating observer sees the temperature Unruh predicted. *Then*
> Verlinde's entropy formula holds **exactly when** Newton's second law `F = ma` holds.

Read carefully, this proves neither side. What it proves is that, given the two stated
assumptions, Verlinde's postulate and ordinary inertia are *the same statement* — you cannot
accept one and reject the other. Every result below has this shape. The value of an
equivalence is that it shrinks the debate: instead of arguing about a long chain of
reasoning, you argue about a short, explicit list of assumptions. That list is given at the
end of this guide.

## The results

### 1. The starting assumptions

Three definitions set the vocabulary; everything else is conditional on them.

- **The entropic-force rule.** A force is what you get from an entropy change `ΔS` at
  temperature `T` across a displacement `Δx`: namely `F = T·ΔS/Δx`. This is the heart of the
  entropic picture — the analogue of "pressure comes from counting molecules."
- **The Unruh temperature.** An observer accelerating at rate `a` sees thermal radiation at
  temperature `T = ħa/(2πk_B c)`. This is standard (though experimentally unconfirmed)
  quantum field theory.
- **The screen temperature.** A screen storing `N` bits about a mass `M` is assigned
  temperature `T = 2Mc²/(N·k_B)` — energy shared equally among the bits. This
  "equipartition" rule is a modeling choice, and the repository labels it as one.

A first structural fact is proved right here: written through these rules, the force law
contains **no Newton's constant at all**. `G` only ever enters later, through the *number of
bits* assigned to a screen. That observation drives everything below.

*In the code:*
[`Physlib/Thermodynamics/VerlindeEntropicForce.lean`](../Physlib/Thermodynamics/VerlindeEntropicForce.lean)
and [`NewtonGIsolation.lean`](../Physlib/Thermodynamics/NewtonGIsolation.lean)
(`verlindeEntropicForce`, `unruhTemperature`, `bitScreenTemperature`,
`entropicForce_bitForm`, `newtonG_isolated`).

### 2. Verlinde's entropy formula is not a free choice

Verlinde postulated that moving a mass `m` by a distance `Δx` changes a screen's entropy by
`ΔS = 2πk_B (mc/ħ)·Δx`. This looked like the most arbitrary step of his paper. The
repository proves it is not arbitrary at all:

> Given the entropic-force rule and the Unruh temperature, the entropic force reproduces
> `F = ma` at every acceleration **if and only if** the entropy formula is exactly
> Verlinde's.

So within the entropic picture, his postulate and Newton's second law are equivalent — there
was never a second option. The theorem is stated carefully at its edges: at zero acceleration
the equation degenerates (every entropy formula trivially works, and the theorem quantifies
over all accelerations precisely to handle this), and the module states explicitly what it
does **not** prove — in particular, it determines a single number `ΔS`, not the full
entropy-gradient field Verlinde's picture imagines.

*In the code:*
[`DisplacementEntropyFromUnruhInertia.lean`](../Physlib/QuantumMechanics/ComplexAction/ComptonClock/DisplacementEntropyFromUnruhInertia.lean)
(`verlindeEntropy_iff_inertial_response_law`, and
`not_existsUnique_displacementEntropy_at_zero_acceleration` for the degenerate case).

### 3. Building the screen out of quantum uncertainty

Where do the screen's "bits" come from? The construction here: a measurement screen that
localizes particles with Gaussian uncertainty of width `σ₀` has a natural information
density (in the Fisher-information sense — the statistician's measure of how much a
measurement can tell you). Tiling a spherical surface with cells of that density and applying
the rules of §1 yields a force with Newton's exact `1/R²` form, with coupling constant
`G = ħcσ₀⁴`.

This is a *construction*, not a derivation of gravity: the tiling rule — "these cells are the
independent bits" — is an assumption, and the repository's metadata flags every result that
depends on it.

*In the code:*
[`GaussianFisherGravitationalResponse.lean`](../Physlib/QuantumMechanics/ComplexAction/ComptonClock/GaussianFisherGravitationalResponse.lean)
(`comptonBitDensity`, `tiledScreen_gravitationalResponse`, `operational_newtonG_eq_info`).

### 4. Why the Planck scale appears

If the constructed coupling `ħcσ₀⁴` is to *be* Newton's constant, how wide must the screen's
cells be? Exactly the Planck width, `σ₀ = (G/ħc)^{1/4}` — and the identification holds **if
and only if** the screen stores precisely one bit per Planck area, the density long
conjectured in black-hole thermodynamics. The width is unique: any other choice gives a
measurably different force, which is what makes the identification falsifiable rather than a
relabeling.

*In the code:*
[`GaussianFisherPlanckCalibration.lean`](../Physlib/QuantumMechanics/ComplexAction/ComptonClock/GaussianFisherPlanckCalibration.lean)
(`identification_iff_planckDensity`, `existsUnique_calibration`).

### 5. Black holes as a cross-check

Any information-based account of gravity must reproduce the two facts we believe about black
holes on independent grounds. It does: counting the §3 cells on a black-hole horizon gives
exactly the Bekenstein–Hawking entropy (area over four Planck areas), and the screen
temperature of §1 evaluated at the horizon is exactly Hawking's temperature. These are
consistency checks — they inherit the tiling assumption — but the program would have died
here, and did not.

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

Read the direction honestly: these theorems take the `1/R²` law as *input* and show
holography is the only bookkeeping that produces it. They are why the holographic structure
is not adjustable — not an independent explanation of why gravity is inverse-square.

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

The least-tested assumption in the whole stack is Unruh thermality (§1). The repository
formalizes exactly where it becomes measurable: a detector of mass `m` accelerating at `a`
responds thermally only above the threshold where the Unruh temperature reaches the
detector's own Compton temperature — below it, the response is exponentially suppressed by
precisely the ratio of the two. This "welding point" is the regime targeted by a 2025
proposal to simulate a low-mass detector in a superconducting qubit (arXiv:2512.17959),
which makes the thermality premise falsifiable rather than philosophical.

*In the code:*
[`Physlib/Thermodynamics/UnruhDetectionThreshold.lean`](../Physlib/Thermodynamics/UnruhDetectionThreshold.lean)
(`suppressionScale_eq_temperatureRatio`, `detectionThreshold_iff_temperatures_weld`).

## What is assumed — the complete list

Everything above is conditional on four assumptions, stated here in plain terms. Accept
them, and the theorems make the rest mathematics. Doubt the program, and this is the
complete list of places to aim.

1. **Forces are entropy gradients** — the rule `F = T·ΔS/Δx` (§1). The founding premise;
   nothing here derives it.
2. **Screens are thermal** — the Unruh temperature is real and the equipartition rule for
   screen bits is right (§1). The Unruh half is testable (§10); equipartition is a model
   choice.
3. **The cell tiling counts bits** — the Gaussian-measurement cells of §3 are the screen's
   independent degrees of freedom. This is the assumption with the widest reach in the
   repository's dependency audit.
4. **One cell identification is left open** — the entropy of §2 is "2π nats per Compton
   wavelength of the *probe mass*"; the screen cells of §3 belong to the *screen's* inference
   scale. Identifying the two is a physical step the repository deliberately does **not**
   take, and says so wherever it matters.

## What is *not* claimed

- No claim that gravity **is** entropic — only that, granted the list above, the entropic
  picture is uniquely rigid: Verlinde's postulates are forced, the holographic count is
  forced, the couplings are forced.
- No derivation of the inverse-square law from first principles — in §6 it is the
  *hypothesis*.
- No proof of Unruh thermality — that is physics, and it is pointed at an experiment (§10).

## Check it yourself

```bash
lake build                      # the whole library; no `sorry`, no `axiom` declarations
./scripts/zil-graph-report.sh   # regenerate the audit report: analysis/zil-graph-report.md
```

Every claim in the program carries machine-readable metadata naming its assumptions and
support. The audit sweeps the full library and reports, among other things, any exact claim
that silently rests on a weaker one ("buried conditionality" — currently zero). The audit
engine itself is proved correct against its reference semantics
([`Physlib/Meta/ZilDatalogFastEquiv.lean`](../Physlib/Meta/ZilDatalogFastEquiv.lean),
`deriveProgramFast_eq`), so trusting the report does not require trusting a script.

# Relational quantum causal dynamics: core formulation and research program

This note states the proposal entirely in the standard language of quantum
physics, quantum information, statistical mechanics, relativity, and
gravitation. The intended object is a background-independent relational quantum
many-body model with causal-network kinematics, local interactions, and
decoherent semiclassical sectors.

The formulation distinguishes four levels of physical statement:

- a **kinematic definition** specifies states, observables, events, and causal
  relations;
- a **dynamical postulate** specifies an action, Hamiltonian, quantum channel,
  or transition law;
- a **derived result** follows from the stated kinematics and dynamics; and
- a **phenomenological identification** relates a derived quantity to an
  experimentally defined observable and must survive dimensional, statistical,
  and empirical tests.

A Born probability, Lorentz transformation, entropy law, or gravitational
coupling is not emergent when it has merely been inserted into the dynamics.

## 1. Physical classification

The most accurate standard classification is:

> a relational, background-independent quantum many-body framework on a causal
> interaction network, with information-theoretic local observables,
> decoherence-defined semiclassical sectors, and a proposed hydrodynamic and
> gravitational continuum limit.

The framework is quantum by default. Its global state may contain many
approximately classical decoherent sectors. These sectors may be described as
Everett branches when their environmental records are stable and mutually
orthogonal to the required approximation. If small off-diagonal interactions
between sectors are retained, the more precise description is a system of
**weakly coupled decoherent sectors**, not strictly autonomous many worlds.

No background spacetime or external universal clock is required at the
kinematic level. Spacetime geometry, particle content, and thermodynamic fields
are continuum observables to be reconstructed from correlations, causal order,
and coarse-grained dynamics.

## 2. Quantum kinematics

Let the physical system be described by a Hilbert space \(\mathcal H\), or more
generally by a net of local observable algebras \(\{\mathcal A_i\}\). A tensor
factorization

```math
\mathcal H \simeq \bigotimes_i \mathcal H_i
```

is useful for finite models but is not fundamental in gauge theory or algebraic
quantum field theory, where local algebras and their inclusions are the safer
objects.

The primitive physical quantities are:

| Quantity | Physical role |
| --- | --- |
| Local subsystem \(\mathcal H_i\) or algebra \(\mathcal A_i\) | Degrees of freedom accessible in one local region. |
| State \(\rho\) | Positive normalized density operator, or a positive normalized functional on the observable algebra. |
| Observable \(O_i\) | Self-adjoint local quantity with experimentally defined outcomes. |
| Quantum channel \(\mathcal E_{j\to i}\) | Completely positive trace-preserving propagation or interaction map. |
| Interaction event \(e\) | A localized coupling, preparation, scattering, or measurement event. |
| Relational clock \(\tau_i\) | A monotone physical record used to order events along one subsystem history. |
| Phase \(\phi_i\) | A cyclic degree of freedom whose differences can enter interference observables. |
| Local generator \(H_i\) | Hamiltonian or effective generator of local evolution. |
| Propagation speed \(c_*\) | Maximum characteristic speed of causal influence in the effective geometry. |

A finite local state at relational tick \(n\) may be written schematically as

```math
\Sigma_i(n)
=\bigl(\rho_i(n),\phi_i(n),\tau_i(n),H_i,
\{\mathcal E_{j\to i}\}_j\bigr).
```

The integer \(n\) labels successive local interactions. It is not a preferred
global time coordinate.

## 3. Local interactions and information response

A local interaction with an incoming physical carrier \(C\) is represented by
a unitary dilation

```math
\rho_i'=
\operatorname{Tr}_{C}
\left[U_{iC}(\rho_i\otimes\rho_C)U_{iC}^{\dagger}\right],
```

or equivalently by a completely positive trace-preserving map

```math
\rho_i'=\mathcal E_{iC}(\rho_i\otimes\rho_C).
```

This representation states whether information remains in correlations with an
environment, is transported to another subsystem, or is inaccessible after a
partial trace. Apparent nonunitarity at the local level is compatible with
unitary evolution of a larger closed state.

The correlation between subsystems \(A\) and \(B\) is quantified by quantum
mutual information

```math
I(A:B)_\rho
=S(\rho_A)+S(\rho_B)-S(\rho_{AB})
=D\!\left(\rho_{AB}\middle\|\rho_A\otimes\rho_B\right),
```

where

```math
S(\rho)=-\operatorname{Tr}(\rho\log\rho),
\qquad
D(\rho\|\sigma)
=\operatorname{Tr}\!\left[\rho(\log\rho-\log\sigma)\right].
```

Thus relative entropy supplies operational distinguishability, while mutual
information measures total correlation. Neither quantity is itself a new form
of matter or a dynamical law. It affects evolution only through an explicitly
specified interaction or effective action.

### 3.1 Phase dynamics

A dimensionally consistent phase increment is generated by action:

```math
\Delta\phi_i=\frac{\Delta S_i}{\hbar}
=-\frac{1}{\hbar}\int_{\tau_i}^{\tau_i+\Delta\tau_i}
E_i(\tau)\,d\tau.
```

At a coarse-grained level, an information-sensitive effective response can be
parameterized by an energy functional such as

```math
H_{\mathrm{int}}
=g_I\,\mathcal F\!\left(I(A:B),D(\rho\|\sigma),\chi\right),
```

where \(g_I\) carries the required energy dimension and \(\chi\) denotes other
local fields or conserved densities. The corresponding phase is

```math
\Delta\phi_I=-\frac{1}{\hbar}\int H_{\mathrm{int}}\,d\tau.
```

Because mutual information and relative entropy depend on the state,
\(H_{\mathrm{int}}[\rho]\) would define nonlinear effective evolution if used
directly. A fundamental linear quantum theory must instead specify
state-independent coupling operators and derive this functional after
coarse-graining or eliminating environmental degrees of freedom.

A factor depending on the number of coupled modes is physically justified only
when it follows from state normalization, a density of states, collective-mode
diagonalization, or a renormalization calculation.

## 4. Relational time and causal order

Localized events carry a partial order. If event \(e_a\) can causally influence
event \(e_b\), write

```math
e_a\prec e_b.
```

Along a local worldline or subsystem history,

```math
e_a\prec_i e_b
\quad\Longrightarrow\quad
\tau_i(e_a)<\tau_i(e_b).
```

There need not be a physically preferred total ordering of spacelike-separated
events. A causal network consists of interaction events and propagation links;
its transitive closure defines causal ancestry. In a continuum regime the
network should approximate the causal order of a Lorentzian manifold.

For effective spatial separation \(d\), causal propagation requires

```math
\Delta t\geq\frac{d}{c_*}.
```

In a local quantum field theory this is strengthened to microcausality,

```math
[O(x),O(y)]=0
\qquad\text{for spacelike-separated }x,y.
```

### 4.1 Quantized relational clocks

An explicit quantum clock is a physical subsystem \(C\) correlated with a
system \(S\). For a stationary global constraint

```math
(H_C+H_S)|\Psi\rangle=0,
```

the conditional system state at a clock reading \(\tau\) is

```math
|\psi_S(\tau)\rangle
\propto\langle\tau|_C\Psi\rangle.
```

If the clock observable has a discrete spectrum, relational duration is
resolved in finite ticks. Such discreteness quantizes the clock record; it does
not by itself prove that spacetime is fundamentally discrete. A physical time
quantum requires a spectrum, a calibration to proper time, and an operational
resolution theorem.

## 5. Global state and decoherent semiclassical sectors

A global pure state can be decomposed relative to a chosen system-environment
split as

```math
|\Psi\rangle
=\sum_\alpha c_\alpha
|\psi_\alpha\rangle_S|E_\alpha\rangle.
```

Decoherence occurs when

```math
\langle E_\beta|E_\alpha\rangle\simeq0
\qquad(\alpha\neq\beta),
```

so interference between the reduced semiclassical sectors becomes negligible
for the selected observables. Approximate classicality requires more than this
orthogonality: the sector states must also remain stable under environmental
monitoring and support approximately classical histories.

Quantum Darwinism adds the requirement that many disjoint environmental
fragments redundantly encode the same pointer observable, in the standard
decoherence-theory sense. The redundancy of records gives multiple local
observers access to consistent classical data.
This is a physical criterion involving mutual information and environmental
fractions, rather than a semantic identification of a sector as classical.

Strict Everettian branches do not interact after ideal decoherence. Weak
inter-sector interaction requires an explicit Hamiltonian

```math
H=\sum_\alpha H_\alpha
+\varepsilon\sum_{\alpha\neq\beta}V_{\alpha\beta},
\qquad |\varepsilon|\ll1.
```

The off-diagonal terms can produce recoherence, tunnelling, or observable
departures from autonomous semiclassical evolution. Their magnitude and
selection rules are therefore empirical content, not interpretation alone.

## 6. Continuum and hydrodynamic limits

Coarse-grained conserved densities should satisfy continuity equations such as

```math
\partial_t n+\nabla\!\cdot j=0,
```

with constitutive relations determined by the microscopic state, symmetries,
and transport coefficients. A hydrodynamic limit is established by identifying
slow conserved modes, a separation of scales, local equilibration, and a
controlled continuum approximation.

A decoherent sector may support an effective hydrodynamic spacetime. It is not
itself an additional geometric dimension. Distinct sectors may instead be
represented as components, sheets, superselection sectors, or coupled phases of
one underlying quantum theory, depending on their operator algebra and
dynamics.

### 6.1 Chirality and antiparticles

Chirality is defined through the Lorentz representation of fermionic fields and
the eigenvalues of \(\gamma^5\). Antiparticles are positive-energy excitations
associated with the charge-conjugate field components; their additive internal
quantum numbers are reversed when those quantum numbers are nonzero. These are
standard properties within a single quantum field theory.

Identifying an antiparticle with a particle excitation in a different
decoherent sector is an additional physical hypothesis. To make it precise one
must construct a map

```math
\mathcal C_{\alpha\beta}:
\mathcal H_{\alpha,\mathrm{particle}}
\longrightarrow
\mathcal H_{\beta,\mathrm{antiparticle}}
```

that preserves the relevant mass shell, reverses the appropriate internal
charges, has the required action on chirality, and reproduces CPT-sensitive
scattering amplitudes. Without such a map and a measurable inter-sector
coupling, the statement is not equivalent to the standard antiparticle
interpretation.

## 7. Stationary states, phases, and critical behavior

A stationary quantum state satisfies

```math
[H,\rho]=0,
```

or, for open dynamics generated by a Lindbladian \(\mathcal L\),

```math
\mathcal L(\rho_*)=0.
```

An energy eigenstate satisfies \(H|E\rangle=E|E\rangle\), while a limit cycle
or time-crystalline phase has different dynamical content. These notions should
not be interchanged merely because each can display a regular phase evolution.

Nonlinear effective dynamics may exhibit bifurcations, critical points,
metastable phases, and attractors. In a closed finite quantum system, exact
unitary evolution is quasiperiodic rather than dissipatively attractive;
attractors arise in reduced, open, coarse-grained, or thermodynamic-limit
dynamics.

## 8. Measurement and nonclassical correlations

A local measurement with setting \(a\) is represented by a positive-operator
valued measure \(\{E_x^{(a)}\}\):

```math
p(x|a)=\operatorname{Tr}\!\left(\rho E_x^{(a)}\right),
\qquad
\sum_xE_x^{(a)}=\mathbf 1.
```

This is the Born rule. A model may take it as part of quantum kinematics or seek
an independent envariance-based or operational derivation, but the two logical
statuses must not be conflated.

For a spin-singlet state,

```math
E(a,b)=-a\!\cdot b,
```

and suitable coplanar settings give the Tsirelson value

```math
|S_{\mathrm{CHSH}}|=2\sqrt2.
```

A valid Bell analysis must state the preparation, setting distribution,
measurement operators, sampling rule, and causal separation. Shared preparation
explains correlation but does not by itself reproduce the quantum correlation
function.

No-signalling requires

```math
\sum_y p(x,y|a,b)
=\sum_y p(x,y|a,b')
```

for all remote settings \(b,b'\). In quantum theory this follows for local
trace-preserving operations on a tensor-product state. In an effective
inter-sector theory it must be rechecked because off-diagonal couplings may
change the causal structure.

## 9. Relativistic kinematics and emergent geometry

A finite propagation speed alone does not establish Lorentz invariance. A
continuum regime must exhibit an invariant causal cone, operational rods and
clocks, and transformations that preserve the interval

```math
ds^2=-c^2dt^2+d\mathbf x^2.
```

For inertial frames in one spatial dimension,

```math
t'=\gamma\left(t-\frac{vx}{c^2}\right),
\qquad
x'=\gamma(x-vt),
\qquad
\gamma=(1-v^2/c^2)^{-1/2}.
```

In a curved continuum limit, the causal order determines the conformal class of
the Lorentzian metric under the hypotheses of causal-reconstruction theorems.
A volume element or equivalent scale observable is additionally required to recover
the full metric. The Alexandrov--Zeeman rigidity result constrains causal
automorphisms of Minkowski spacetime; it does not by itself supply curvature or
the Einstein dynamics.

## 10. Entropy, scale, and thermodynamic behavior

For a reduced state \(\rho_A\), the entanglement entropy is

```math
S_A=-\operatorname{Tr}(\rho_A\log\rho_A).
```

For a classical coarse-grained ensemble \(\{p_\omega\}\),

```math
S_{\mathrm{Shannon}}
=-\sum_\omega p_\omega\log p_\omega.
```

Entropy can grow with region size, but the scaling depends on the state and
dynamics. Thermal entropy is normally extensive, ground-state entanglement in a
local gapped theory typically obeys an area law, and critical or long-range
states can carry logarithmic or stronger corrections.

Mutual information also does not increase universally with geometric scale.
What is universal is positivity and monotonicity under local quantum channels:

```math
D(\rho\|\sigma)
\geq D(\mathcal E(\rho)\|\mathcal E(\sigma)).
```

Consequently, increasing the number of accessible degrees of freedom can
increase total information capacity, while coarse-graining cannot increase
distinguishability. Any proposed scale law must specify which subsystems,
states, channels, and coarse-grainings are being compared.

An arrow of time can arise from low-entropy boundary conditions, environmental
entanglement, kinetic limits, and coarse-grained irreversibility. It does not
follow merely from unitary quantum evolution.

## 11. Thermodynamic and gravitational sector

An entropic force is a constitutive relation

```math
F=T\,\nabla S.
```

Recovering Newtonian gravity requires a specific temperature law,
entropy-displacement relation, screen geometry, and degree-of-freedom count.
Recovering Einstein gravity further requires a local horizon construction,
Clausius relation, stress-energy flux, metric variation, and a continuum
equation-of-state argument.

The screen degree-of-freedom count can be estimated in two ways:

```math
N_{\mathrm{th}}=\frac{2E}{k_BT},
\qquad
N_C=\frac{A}{\lambda_C(m)^2},
\qquad
\lambda_C(m)=\frac{\hbar}{mc}.
```

The first is an equipartition count. The second assigns one transverse mode to
each squared reduced-Compton resolution length. They describe the same screen
only under the explicit compatibility condition

```math
\frac{2E}{k_BT}=\frac{A}{\lambda_C(m)^2}.
```

This gives the \(G\)-free relation

```math
k_BT=\frac{2E\lambda_C(m)^2}{A}.
```

If a holographic gravitational readout is then defined by

```math
G_{\mathrm{scr}}=\frac{Ac^3}{\hbar N},
```

the compatible count gives

```math
G_{\mathrm{scr}}
=\frac{Ac^3k_BT}{2E\hbar}
=\frac{\hbar c}{m^2}.
```

This is a conditional scale identity. It becomes a prediction only if the mass
scale and the one-mode-per-cell identification are fixed independently of the
target gravitational coupling.

## 12. Schwarzschild, Bekenstein--Hawking, and Susskind consistency

For a Schwarzschild black hole of mass \(M\), distinguish the black-hole mass
from the Compton calibration mass \(m\):

```math
r_s=\frac{2GM}{c^2},
\qquad
A_H=4\pi r_s^2
=\frac{16\pi G^2M^2}{c^4},
\qquad
T_H=\frac{\hbar c^3}{8\pi GMk_B}.
```

With \(E=Mc^2\), the thermodynamic count is

```math
N_{\mathrm{th}}
=\frac{2Mc^2}{k_BT_H}
=\frac{16\pi GM^2}{\hbar c}
=\frac{A_Hc^3}{G\hbar}.
```

The Compton-cell count is

```math
N_C
=\frac{A_H}{\lambda_C(m)^2}
=\frac{16\pi G^2M^2m^2}{\hbar^2c^2}.
```

Their equality is equivalent, for positive scales, to

```math
m^2=\frac{\hbar c}{G},
\qquad
\lambda_C(m)^2=\frac{G\hbar}{c^3}=\ell_P^2.
```

The black-hole mass cancels. The compatible Compton calibration is the Planck
mass, not the mass of the black hole. If \(m=M\), then

```math
\frac{N_C}{N_{\mathrm{th}}}=\frac{M^2}{m_P^2},
```

so the black hole's own Compton wavelength gives the required count only for a
Planck-mass black hole.

The raw cell count \(N\) and the entropy are not identical. With one quarter
nat per area cell,

```math
S_{\mathrm{BH}}^{(\mathrm{nats})}
=\frac{N}{4}
=\frac{A_Hc^3}{4G\hbar}
=\frac{A_H}{4\ell_P^2}
=\frac{4\pi GM^2}{\hbar c}.
```

Restoring the Boltzmann constant gives

```math
S_{\mathrm{BH}}^{(\mathrm{phys})}
=k_BS_{\mathrm{BH}}^{(\mathrm{nats})},
\qquad
Mc^2=2T_HS_{\mathrm{BH}}^{(\mathrm{phys})},
```

which is the Schwarzschild Smarr relation.

For the right-angle Compton shift

```math
\delta_m=\Delta\lambda_m(\pi/2)=2\pi\lambda_C(m),
```

the count and entropy take the operational forms

```math
N_C=\frac{4\pi^2A_H}{\delta_m^2},
\qquad
S_{\mathrm{BH}}^{(\mathrm{nats})}
=\frac{\pi^2A_H}{\delta_{m_P}^2}.
```

All entropies in the following bounds are dimensionless entropies in nats. The
Susskind collapse process uses the generalized second law. If matter and a
nonnegative-entropy shell collapse to a black hole filling a spherical screen,

```math
S_{\mathrm{matter}}+S_{\mathrm{shell}}
\leq S_{\mathrm{final}},
\qquad
S_{\mathrm{shell}}\geq0,
```

then

```math
S_{\mathrm{matter}}
\leq\frac{Ac^3}{4G\hbar}.
```

Under compatibility of the thermodynamic and Compton counts, the same ceiling
can be written

```math
S_{\mathrm{matter}}
\leq\frac{N}{4}
=\frac{E}{2k_BT}
=\frac{A}{4\lambda_C(m_P)^2}
=\frac{\pi^2A}{\delta_{m_P}^2}.
```

The Bekenstein energy-radius bound

```math
S_{\mathrm{matter}}\leq\frac{2\pi ER}{\hbar c}
```

and the Susskind spherical bound both saturate at \(E=Mc^2\) and \(R=r_s\).
This agreement is a black-hole consistency condition. It is not an independent
measurement of horizon microstates: Compton scattering fixes a resolution
length, while assigning one independent horizon degree of freedom per squared
resolution length remains a physical discretization hypothesis.

## 13. Units and physical parameters

The fundamental conversion scales are the speed \(c\), reduced Planck constant
\(\hbar\), and Boltzmann constant \(k_B\). Other parameters must be defined by
the action or by operational observables:

| Quantity | Symbol | Physical meaning |
| --- | --- | --- |
| Proper-time resolution | \(\Delta\tau\) | Smallest resolved interval of a specified relational clock. |
| Length resolution | \(\ell_*\) | Spatial resolution of a specified scattering or localization experiment. |
| Energy scale | \(E_*\) | Spectral gap, rest energy, or interaction scale. |
| Propagation speed | \(c_*\) | Characteristic causal speed of the effective medium. |
| Interaction coupling | \(g_I\) | Coefficient of the information-dependent interaction Hamiltonian. |
| Inter-sector coupling | \(\varepsilon\) | Off-diagonal coupling between decoherent sectors. |

Natural units \(c=\hbar=k_B=1\) may be used only after every observable has a
dimensionally complete definition. Dimensionless couplings must be obtained
from ratios of independently defined physical scales.

## 14. Finite and numerical realizations

A finite realization can be studied as an open quantum lattice system or a
quantum causal network:

1. Specify local Hilbert spaces, the initial density operator, interaction
   graph, and boundary conditions.
2. Specify local Hamiltonian terms or completely positive transition maps.
3. Enforce causal locality and the characteristic propagation speed.
4. Evolve by a controlled product formula, tensor-network method, quantum
   trajectory, or exact diagonalization.
5. Record relational clock observables, correlation functions, conserved
   currents, entropies, and phase-sensitive observables.
6. Repeat over physical initial ensembles and increasing system sizes.
7. Test discretization error, finite-size scaling, boundary sensitivity, and
   independence from an arbitrary numerical foliation.

Relativistic symmetry, Bell correlations, hydrodynamics, and gravitational
response should be tested separately before their simultaneous continuum limit
is claimed.

## 15. Validation targets

| Physical target | Required evidence |
| --- | --- |
| Quantum consistency | Positive normalized states and completely positive trace-preserving local dynamics. |
| Causal consistency | No observable response outside the causal past; microcausality in the continuum limit. |
| Relational time | A physical clock observable, conditional evolution, and a controlled clock-resolution limit. |
| Decoherent sectors | Suppressed interference, stable records, and a quantified decoherence timescale. |
| Quantum Darwinism | Redundant environmental records quantified across disjoint fragments. |
| Inter-sector interaction | Explicit off-diagonal Hamiltonian terms and predicted recoherence or transition observables. |
| Stationary regime | A Hamiltonian eigenstate, invariant density operator, or Lindblad fixed point under the stated dynamics. |
| Bell correlation | A joint preparation and measurement protocol reproducing the correlation and no-signalling marginals. |
| Lorentz symmetry | An invariant causal cone, interval, and transformation group recovered in the continuum regime. |
| Hydrodynamic limit | Conserved slow modes, local equilibration, constitutive relations, and controlled scaling. |
| Antiparticle identification | Charge conjugation, CPT behavior, mass-shell preservation, and scattering amplitudes. |
| Thermodynamic behavior | Defined ensemble, entropy production law, temperature, and coarse-graining. |
| Gravitational response | A local horizon law, stress-energy coupling, metric dynamics, and Newtonian limit. |
| Black-hole sector | Correct Hawking temperature, area entropy, Smarr relation, first law, and entropy bounds with all assumptions disclosed. |

## 16. Dependency structure and open problems

The physical development should proceed through the following dependency chain:

1. local quantum states, observable algebras, and channels;
2. causal order and relational clock observables;
3. unitary or open-system dynamics and conserved quantities;
4. decoherence, environmental records, and semiclassical sectors;
5. nonclassical correlations and measurement theory;
6. hydrodynamic and Lorentzian continuum limits;
7. local thermodynamics and horizon entropy;
8. gravitational field equations and black-hole consistency tests.

The principal unresolved physical questions are:

- Which microscopic Hamiltonian produces the proposed information-dependent
  phase response?
- Does a controlled continuum limit recover local Lorentz symmetry?
- Which degrees of freedom carry the relational clock, and what limits its
  accuracy?
- Can stable decoherent sectors coexist with a nonzero observable inter-sector
  coupling?
- Does environmental redundancy yield an objective semiclassical field
  configuration in the quantum-Darwinist sense?
- Can a hydrodynamic limit produce an effective Lorentzian metric rather than
  merely propagation on a fixed graph?
- Can a cross-sector charge-conjugation map reproduce standard antiparticle
  scattering and CPT constraints?
- Which entropy law follows from the microscopic state and dynamics rather than
  from an imposed area count?
- Can the Compton-resolution cell be identified with an independent horizon
  degree of freedom without using the measured value of \(G\)?
- Can local Clausius balance and stress-energy flux determine the nonlinear
  Einstein dynamics with controlled boundary and variation hypotheses?

The immediate target is a fully specified local quantum dynamics with a
relational clock and causal propagation law. Its decoherence, continuum,
thermodynamic, and gravitational limits should then be derived in that order.

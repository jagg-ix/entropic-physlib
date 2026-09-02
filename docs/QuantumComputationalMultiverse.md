# Quantum-computational interacting-worlds framework

This note specifies a quantum-first ontology in standard technical language.
The fundamental object is a quantum multiverse whose approximately classical
world-sectors are weakly coupled, hydrodynamic, and chiral. Global quantum
evolution is interpreted as computation; decoherence and redundant
environmental records account for the emergence of branch-relative classical
descriptions.

The framework combines established mathematical tools with additional physical
hypotheses. It is therefore important to distinguish standard quantum
formalism, interpretive choices, and proposed new dynamics.

## 1. Classification

The formulation can be classified as a:

- quantum-computational ontology;
- pregeometric and relational quantum model;
- many-interacting-worlds or interacting-sector framework;
- quantum-hydrodynamic formulation;
- decoherent-histories and quantum-Darwinist account of classicality; and
- chiral multiverse model with a proposed cross-sector interpretation of
  antiparticles.

It is not simply a classical simulation, a cellular automaton, or an ordinary
Everett interpretation. Its weak intersector coupling is an additional
dynamical element: effectively classical sectors participate in the global
quantum evolution rather than becoming permanently independent worlds.

## 2. Status vocabulary

This note uses four levels of commitment:

- **Standard formalism** denotes established mathematical machinery of quantum
  theory.
- **Interpretation** assigns an ontology to mathematical structures without
  necessarily changing observable predictions.
- **Postulate** adds a rule or structure that defines this particular
  formulation.
- **Derivation target** is a result that the formulation should reproduce but
  that does not follow merely from its vocabulary.

In particular, hydrodynamic rewriting does not by itself derive interacting
worlds, and opposite chirality does not by itself establish a
particle--antiparticle relation.

## 3. Global quantum state

Let \(\mathcal H\) be the Hilbert space of the complete system. The universal
state is represented schematically as

\[
|\Psi\rangle
=\sum_{b\in\mathcal B}\alpha_b
|U_b,\chi_b\rangle,
\]

where:

- \(b\) labels an approximately classical world-sector;
- \(U_b\) denotes the sector's matter, field, and record configuration;
- \(\chi_b\) is a chirality or orientation label; and
- \(\alpha_b\) is a complex amplitude.

The decomposition into sectors is approximate and dynamical. It must ultimately
be selected by stable records, decoherence, or another declared criterion; an
arbitrary choice of Hilbert-space basis does not define physically meaningful
worlds.

The complete state, rather than any one sector, is the fundamental quantum
object.

## 4. Intrasector and intersector dynamics

A minimal Hamiltonian decomposition is

\[
H
=\sum_b H_b^{\mathrm{intra}}
+\varepsilon H^{\mathrm{inter}},
\]

or, in a sector representation,

\[
i\hbar\frac{\partial\psi_b}{\partial t}
=H_b^{\mathrm{intra}}\psi_b
+\varepsilon\sum_{b'\ne b}K_{bb'}\psi_{b'}.
\]

Here:

- \(H_b^{\mathrm{intra}}\) generates the effective dynamics within sector \(b\);
- \(K_{bb'}\) couples distinct sectors;
- \(\varepsilon\) controls the coupling scale; and
- Hermiticity or a more general quantum-channel condition must preserve the
  required normalization and positivity.

Three regimes are distinguished:

1. **Coherent regime:** relative phases remain available for interference.
2. **Weak-coupling regime:** sectors are approximately classical but retain
   small observable or virtual intersector effects.
3. **Decoupled limit:** sectors evolve as operationally independent classical
   worlds.

The second regime is the characteristic proposal. Standard Everettian branches
are normally treated as effectively autonomous after decoherence; residual
intersector coupling therefore requires an explicit Hamiltonian, potential, or
quantum channel.

## 5. Hydrodynamic representation

For a scalar sector amplitude, write the polar decomposition

\[
\psi_b
=\sqrt{\rho_b}\,e^{iS_b/\hbar}.
\]

The sector variables are:

- density \(\rho_b\);
- phase or action \(S_b\);
- velocity \(\mathbf v_b=\nabla S_b/m\); and
- current \(\mathbf j_b=\rho_b\mathbf v_b\).

Without intersector transfer, the density satisfies a continuity equation

\[
\frac{\partial\rho_b}{\partial t}
+\nabla\cdot(\rho_b\mathbf v_b)=0.
\]

With intersector exchange, use

\[
\frac{\partial\rho_b}{\partial t}
+\nabla\cdot(\rho_b\mathbf v_b)
=J_b^{\mathrm{inter}},
\qquad
\sum_b J_b^{\mathrm{inter}}=0,
\]

when total norm is conserved. The phase equation takes the schematic form

\[
\frac{\partial S_b}{\partial t}
+\frac{|\nabla S_b|^2}{2m}
+V_b+Q_b+V_b^{\mathrm{inter}}=0,
\]

with quantum potential

\[
Q_b
=-\frac{\hbar^2}{2m}
\frac{\nabla^2\sqrt{\rho_b}}{\sqrt{\rho_b}}.
\]

The scalar Madelung form is only a starting point. Spin, relativistic fields,
gauge symmetry, topology, and chirality require spinorial or field-theoretic
hydrodynamic variables.

The term **world-sector** is preferable to **dimension** unless \(b\) is shown
to behave as an independent coordinate. A sector is a component of the quantum
state or an emergent classical history; a dimension is normally a coordinate
degree of freedom.

## 6. Chirality

Assign each sector an orientation label

\[
\chi_b\in\{-1,+1\},
\]

or a more general chiral charge. Chirality may enter:

- the sign of vorticity or circulation;
- the allowed intersector coupling matrix \(K_{bb'}\);
- parity-sensitive transport coefficients;
- spinor projections;
- boundary or interface dynamics; and
- the definition of conjugate sectors.

The physical meaning of \(\chi_b\) must be fixed. Possible meanings include
spatial handedness, helicity, Weyl chirality, fluid circulation, orientation of
an emergent time coordinate, or a discrete topological charge. These meanings
are not interchangeable.

## 7. Conjugate sectors and antiparticles

Introduce an involution \(b\mapsto\bar b\) pairing sectors. A proposed
conjugation map has the form

\[
\mathsf C:
(b,q,\chi_b,\mathcal F_b)
\longmapsto
(\bar b,-q,-\chi_b,\mathcal F_{\bar b}),
\qquad
\mathsf C^2=1,
\]

where \(q\) denotes additive internal charges and \(\mathcal F_b\) denotes the
sector's field configuration.

The cross-sector antiparticle postulate is:

> An excitation intrinsic to a conjugate chiral sector may be represented in a
> local sector as an antiparticle excitation through an allowed intersector
> coupling.

Operationally,

```text
excitation in a conjugate sector
    -> intersector coupling or exchange current
    -> antiparticle signature in the local sector
```

This proposal must not identify antiparticles with opposite chirality alone.
Charge conjugation and chirality are distinct in relativistic quantum field
theory, and a massive Dirac field contains both chiral components. The proposed
map must reproduce, rather than replace by terminology:

- opposite additive charges;
- equal particle and antiparticle masses and lifetimes where required;
- Lorentz covariance;
- spin--statistics relations;
- local pair creation and annihilation;
- CPT constraints;
- chiral weak interactions; and
- virtual antiparticle contributions to local amplitudes.

One possible mechanism is that local pair creation is the branch-relative
description of a norm- and charge-conserving exchange between \(b\) and
\(\bar b\). Establishing this requires an explicit interaction term and a map
to quantum-field creation and annihilation operators.

## 8. Quantum evolution as computation

The global evolution

\[
|\Psi(t)\rangle
=U(t)|\Psi(0)\rangle
\]

is interpreted as a quantum computation. Sector amplitudes encode alternative
computational histories; their relative phases allow constructive and
destructive interference.

The computational sequence is

```text
coherent alternatives
    -> hydrodynamic propagation within sectors
    -> phase-sensitive intersector coupling
    -> interference
    -> environmental entanglement
    -> stable branch-relative records
```

Calling the multiverse a quantum computer is operationally meaningful only if
the formulation identifies:

- the state space;
- admissible gates or Hamiltonians;
- preserved quantities;
- input and output observables;
- how interference changes outcome weights; and
- how records become accessible to internal observers.

Independent decohered sectors cannot pool their answers. Computational leverage
comes from coherent interference or an explicit residual coupling, not from the
mere number of classical worlds.

## 9. Classicality through decoherence and quantum Darwinism

Interaction with an environment suppresses locally observable coherence between
selected states. Environment-induced superselection identifies stable pointer
observables, while redundant environmental records allow multiple observers to
recover approximately the same classical information.

In this framework, quantum Darwinism supplies a candidate sector-selection
mechanism:

```text
quantum state
    -> environmental monitoring
    -> stable pointer observables
    -> redundant records
    -> intersubjectively accessible classical sector
```

Darwinian fitness here means stability and redundant record proliferation. It
does not mean that universes biologically reproduce, possess goals, or are
selected for moral properties.

The redundancy of a record can be studied through quantum mutual information,
Holevo information, or accessible information between a system and fragments of
its environment.

## 10. Quantum information and access channels

Before measurement, correlations are described using density operators and
quantum information measures. Quantum relative entropy is

\[
D(\rho\|\sigma)
=\operatorname{Tr}
\bigl[\rho(\log\rho-\log\sigma)\bigr],
\]

and quantum mutual information is

\[
I(A:B)
=D(\rho_{AB}\|\rho_A\otimes\rho_B)
=S(\rho_A)+S(\rho_B)-S(\rho_{AB}).
\]

Directed access to quantum information should be represented by quantum
channels, controlled interactions, or operator-algebra inclusions rather than
by unrestricted copying. Arbitrary unknown quantum states cannot be cloned.

An internal observer is an open quantum subsystem able to acquire, retain, and
process records. Its accessible classical history is branch-relative even
though its underlying state belongs to the global quantum evolution.

## 11. Decisions in the interacting-worlds picture

A quantum decision distributes alternatives across coherent sectors:

\[
|\Psi_0\rangle
=\sum_a\alpha_a|a\rangle|0\rangle,
\]

evaluates them reversibly,

\[
|a\rangle|0\rangle
\longmapsto
|a\rangle|q_a\rangle,
\]

and converts the evaluations into phases or amplitudes. Interference changes the
weights \(\alpha_a\mapsto\beta_a\), after which environmental entanglement
produces stable relative records:

\[
\sum_a\beta_a
|a\rangle|M_{\mathrm{ready}}\rangle|E_0\rangle
\longmapsto
\sum_a\beta_a
|a\rangle|M_a\rangle|E_a\rangle.
\]

There is one branch-relative commitment in each stable record sector, rather
than one global outcome that deletes all alternatives. A theory of rational
choice must specify how branch weights enter evaluation; Born-weighted expected
utility is a candidate rule, not a consequence of the word **decision**.

## 12. Relation between fundamental and emergent descriptions

The framework has three explanatory levels:

| Level | Description |
| --- | --- |
| Fundamental | Global quantum state, unitary or channel evolution, and intersector coupling. |
| Mesoscopic | Chiral quantum fluids, exchange currents, phase relations, decoherence, and stable records. |
| Emergent | Approximately classical worlds containing local observers, particles, fields, and causal histories. |

The classical sectors are not fundamental containers. They are stable,
branch-relative descriptions selected from the global quantum dynamics.
Conversely, the global state must reproduce the effective autonomy and
locality observed within those sectors.

## 13. Consistency requirements

A complete formulation should establish the following interfaces.

### Quantum consistency

- normalized positive states;
- unitary evolution or completely positive trace-preserving dynamics;
- a precise tensor-factor or operator-algebra structure;
- a preferred-sector criterion that is not an arbitrary basis choice; and
- a derivation or explicit postulate of the probability rule.

### Intersector consistency

- an explicit form for \(K_{bb'}\) or the interworld potential;
- conservation of total probability and declared charges;
- a classical limit as coupling or coherence becomes negligible;
- compatibility between residual coupling and decoherence; and
- observable bounds on cross-sector effects.

### Hydrodynamic consistency

- treatment of nodes where \(\rho_b=0\);
- quantized circulation and topology;
- gauge-covariant currents;
- relativistic and spinorial generalization; and
- recovery of the intended wave or field equations.

### Particle-physics consistency

- a precise charge-conjugation operator;
- distinction among charge conjugation, parity, time reversal, helicity, and
  chirality;
- local quantum-field operator reconstruction;
- Standard Model charge assignments and interaction channels; and
- agreement with particle--antiparticle scattering and decay amplitudes.

### Emergent-classical consistency

- decoherence times and pointer observables;
- redundant environmental records;
- branch-relative causal histories;
- effective locality and no-signalling; and
- a controlled continuum and macroscopic limit.

## 14. Status of the ingredients

| Ingredient | Status in this framework |
| --- | --- |
| Hilbert-space states and quantum channels | Standard formalism |
| Relative-state branching | Interpretation |
| Quantum hydrodynamic variables | Standard reformulation with scope limitations |
| Decoherence and pointer-state selection | Standard open-system mechanism |
| Quantum Darwinism | Established research program for redundant classical records |
| Classical worlds with direct interaction | Nonstandard model class related to many-interacting-worlds proposals |
| Persistent residual coupling after classicalization | Model postulate |
| Sector-level chirality | Model postulate requiring a precise definition |
| Antiparticles as conjugate-sector excitations | New interpretive and dynamical hypothesis |
| Recovery of relativistic quantum field theory | Derivation target |
| Consciousness from quantum computation | Separate hypothesis, not part of the required physical core |

## 15. Minimal research program

The smallest useful model should avoid attempting the full relativistic theory
at once:

1. Define finitely many one-dimensional world-sectors with densities and
   phases.
2. Choose a norm-preserving nearest-sector interaction kernel.
3. Recover a known interference or tunneling result.
4. Add environmental degrees of freedom and identify stable record sectors.
5. Measure how record redundancy depends on coupling and decoherence.
6. Introduce a two-valued sector orientation and test parity-sensitive
   transport.
7. Define a conjugate-sector involution and a conserved exchange current.
8. Only then attempt a spinorial field model and a particle--antiparticle
   correspondence.

This sequence separates three questions that should not be conflated:

- Can interacting classical sectors reproduce quantum dynamics?
- Can chiral quantum fluids reproduce relativistic field structure?
- Can conjugate-sector exchange reproduce antiparticle phenomenology?

## 16. Compact statement

The core proposal is a pregeometric quantum multiverse whose global evolution
acts as a computation over weakly coupled chiral hydrodynamic sectors.
Decoherence and redundant environmental records make selected sectors appear
classical to internal observers. Residual intersector dynamics carries the
quantum interference structure, while a proposed conjugation between
oppositely oriented sectors supplies a candidate interpretation of local
antiparticle excitations.

## 17. Foundational comparison points

- Hugh Everett III, “Relative State” Formulation of Quantum Mechanics,
  *Reviews of Modern Physics* 29, 454 (1957),
  <https://doi.org/10.1103/RevModPhys.29.454>.
- E. Madelung, Quantentheorie in hydrodynamischer Form, *Zeitschrift für
  Physik* 40, 322--326 (1927), <https://doi.org/10.1007/BF01400372>.
- Wojciech H. Zurek, Decoherence, einselection, and the quantum origins of the
  classical, *Reviews of Modern Physics* 75, 715 (2003),
  <https://doi.org/10.1103/RevModPhys.75.715>.
- Harold Ollivier, David Poulin, and Wojciech H. Zurek, Environment as a
  Witness: Selective Proliferation of Information and Emergence of Objectivity
  in a Quantum Universe, *Physical Review A* 72, 042113 (2005),
  <https://doi.org/10.1103/PhysRevA.72.042113>.
- Michael J. W. Hall, Dirk-André Deckert, and Howard M. Wiseman, Quantum
  Phenomena Modeled by Interactions between Many Classical Worlds, *Physical
  Review X* 4, 041013 (2014),
  <https://doi.org/10.1103/PhysRevX.4.041013>.

These references supply comparison points, not a derivation of the combined
framework. The cross-sector chirality and antiparticle hypotheses are additional
claims and must be evaluated through their explicit dynamics.

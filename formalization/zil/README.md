# ZIL models for Physlib formalization

This directory tracks formalization arcs outside Lean while leaving all
mathematical proof authority inside Lean's kernel.

The models follow the workflow used by `jagg-ix/zil-lean`:

- Lean declarations may contain canonical `zil attach` annotation blocks.
- `.zc` files record claims, reused APIs, source equations, declaration
  witnesses, dependency edges, rejected omissions, and open targets.
- A `proof:...` token names a Lean declaration. It is not kernel evidence by
  itself and remains `pending_kernel_check` until the corresponding audit builds.
- ZIL records implementation and impact information; it does not replace Lean.

## Pinned ZIL revision

```text
jagg-ix/zil-lean@abfddd3d4466f24e81830c5f96b102938a832565
```

The previous local-development pin `167cf603aba21bb1160cbe68ad1c4ba9056f92e9`
is no longer reachable after the `zil-lean` history rewrite. The reachable pin above
is the revision used by the v4.33 migration build harness and makes clean remote
checkouts reproducible again.

## Evidence closure policy

The CAT/EPT registry adds a stricter lifecycle policy:

1. **Implemented claims** must name a Lean witness.
2. **Rejected omissions** must name a counterexample or resolution edge.
3. **Open analytic obligations** must not carry a proof witness.
4. **Verification state** is distinct from implementation state.
5. **Superseded labels** remain queryable so old status tables can be repaired
   rather than silently overwritten.
6. Embedded Lean records and standalone graphs share stable claim identifiers;
   the Lean registry is the canonical lifecycle inventory.

The Lean implementation is:

```text
Physlib/Meta/ZilEvidenceClosureRegistry.lean
Physlib/Meta/ZilEvidenceClosureRegistryAudit.lean
```

The registry audit connects its closed records to actual theorem declarations
and applies the repository's axiom-clean and non-vacuity checks.

## Available graphs

### CAT/EPT evidence closure

```text
formalization/zil/cat-ept-evidence-closure.zc
```

This graph reconciles the live Hartree-continuity, energy-split no-loss,
Born-normalization, minimizer, compact-orbit, and orbital-stability chain. It
also records three rejected omissions:

- global weak closure of the unit-mass sphere;
- unconditional weak lower semicontinuity of attractive translation-invariant
  energy;
- a bounded `H¹ → H¹` realization of the spatial Schrödinger generator.

The remaining nodes are the genuinely model-specific analytic obligations:
localized strong `L^(6/5)` Born convergence, recentered first-moment control,
the concrete energy-critical Duhamel/Strichartz flow, global mass/energy
conservation, and analytic branch identification.

Useful queries:

- `implementation_registry`
- `resolved_omissions`
- `superseded_open_labels`
- `remaining_obligations`
- `dependency_edges`
- `awaiting_kernel_checks`

### Liouville-space second quantization

```text
formalization/zil/liouville-second-quantization.zc
```

This graph covers discrete matrix units, arbitrary mode indices, finite
occupation sectors, regular continuum kernels, pointwise multiplication, and
continuum matrix units represented by Dirac distributions.

### Lindblad-driven discretized leads

```text
formalization/zil/lindblad-driven-leads.zc
```

This graph follows Schwarz et al., Phys. Rev. B 94, 155142 (2016), and tracks:

- the loss/gain rate identities and one-level occupation fixed point;
- the bounded Hilbert--Schmidt LDDL generator and its exponential evolution;
- one-level Green functions and Lorentzian broadening;
- the continuum-resolution criterion `delta <= gamma < physicalScale`;
- level doubling and preservation of retarded and Keldysh hybridization weights;
- scalar-rate invariance under unitary basis changes;
- existing dense-domain and closability results for pointwise continuum
  multiplication; and
- the remaining discretized-to-continuum convergence theorems.

## Reused formal infrastructure

| Requirement | Existing carrier/API |
|---|---|
| Discrete matrix unit | `Mathlib.Matrix.single` |
| Product-space square-integrable kernel | `MeasureTheory.Lp ℂ 2 (μ.prod μ)` |
| Measurability and finite `L²` norm | `MeasureTheory.MemLp` |
| Spatial continuum Hilbert space | `QuantumMechanics.SpaceDHilbertSpace` |
| Pointwise multiplication with maximal domain | `SpaceDHilbertSpace.mulOperator` |
| Dense-domain theorem | `SpaceDHilbertSpace.mulOperator_hasDenseDomain` |
| Closability theorem | `SpaceDHilbertSpace.mulOperator_isClosable` |
| Continuum-labelled point source | `Physlib.Distribution.diracDelta` |
| Finite-dimensional operator Hilbert space | `HilbertSchmidtOperatorSpace.HSOp` |
| Left/right operator multiplication | `leftMulHS`, `rightMulHS` |
| Bounded-generator exponential | `NormedSpace.exp` |
| Complete continuum `H¹(ℝ³)` | `EuclideanHOneThree` |
| Hartree continuity | `newtonianSelfEnergy_tendsto_of_lsixFifths` |
| Energy-split no-loss | `hOne_tendsto_of_minimizing_energySplit` |
| Born-law compactness | `isCompact_hOneBorn_energyMinimizers_of_interactionClosure` |

## Run a standalone graph

From a checkout of `jagg-ix/zil-lean`:

```bash
./bin/zil \
  /path/to/entropic-physlib-private/formalization/zil/cat-ept-evidence-closure.zc
```

For machine-readable query output:

```bash
./bin/zil export-data \
  /path/to/entropic-physlib-private/formalization/zil/cat-ept-evidence-closure.zc \
  json /tmp/cat-ept-zil.json queries
```

## Scan embedded Lean annotations

```bash
./bin/zil embedded-scan \
  /path/to/entropic-physlib-private/Physlib \
  /tmp/physlib-embedded.zc \
  physlib
```

The scan adds deterministic declaration identities, source hashes, line spans,
and `trust:asserted_annotation`. These metadata support drift detection; they
do not replace Lean elaboration.

## Verification transition

After the relevant Lean audit succeeds, proof records may be changed from
`state:pending_kernel_check` to `state:kernel_checked` in a dedicated
evidence-only commit. Source implementation and verification state must remain
separate.

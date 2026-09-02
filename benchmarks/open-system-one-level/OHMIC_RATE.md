# Finite-Ohmic origin of the one-level rate

## Scope

The one-level relaxation law is

```text
N(t) = f + (N(0) - f) exp(-2 gamma t).
```

The original benchmark protocol allows `gamma` to be fixed from an independent
Lorentzian half-width. The formal library also contains a finite
Caldeira--Leggett Ohmic coupling law:

```text
c^2 = (4 gamma / pi) cutoff^3 / shape_sum.
```

`Physlib.QuantumMechanics.OpenSystems.LindbladDrivenLeads.OhmicMicroscopicRate`
inverts that exact relation:

```text
gamma = pi c^2 shape_sum / (4 cutoff^3).
```

The same derived `gamma` then fixes:

```text
occupation relaxation coefficient = 2 gamma
Lorentzian half-width             = gamma
Lorentzian full width             = 2 gamma
Caldeira--Leggett damping scale   = gamma
binary-KL production coefficient = 2 gamma
```

## Scientific status

The coupling-law inversion and finite-mode cancellation are exact algebraic
results inside the declared finite Ohmic bath model.

The following identification remains a physical model premise:

```text
weak-coupling / Born--Markov / secular reduction
finite Ohmic oscillator-bath gamma
    = effective one-level LDDL gamma
```

The derivation does not by itself establish:

- that a measured system is represented by the finite Ohmic model;
- that the selected transition satisfies the Markovian or secular regime;
- the physical units of the supplied coupling, cutoff, and shape sum;
- experimental source validity;
- physical-state identity;
- a held-out prediction; or
- `external_validated` maturity.

## Source artifact

A microscopic-rate source follows
[`ohmic-rate-source.schema.json`](ohmic-rate-source.schema.json). Its rate block
has the exact identifiers:

```json
{
  "observable": "finite_ohmic_coupling",
  "formula_id": "gamma_eq_pi_coupling_sq_shape_over_4_cutoff_cubed",
  "unit_contract": "coupling_sq_times_shape_over_cutoff_cubed_is_rate",
  "coupling_strength_sq": 0.0,
  "cutoff": 0.0,
  "shape_sum": 0.0,
  "rate_unit": "s^-1"
}
```

The three numerical inputs must be strictly positive. The zero values above are
placeholders illustrating field names, not a valid source artifact.

## Generate the standard calibration artifact

Run:

```bash
python3 scripts/derive_one_level_ohmic_rate.py \
  /path/to/ohmic-calibration-source.json \
  --output-dir /tmp/one-level-ohmic-rate
```

The tool writes:

```text
calibration.json
ohmic-rate-derivation.json
```

`calibration.json` uses the existing benchmark schema and records the derived
`gamma` as the Lorentzian half-width. It also adds lineage IDs containing:

- the source artifact SHA-256;
- the exact formula identifier; and
- the Lean theorem identifier
  `QuantumMechanics.LindbladDrivenLeads.gammaFromOhmicCoupling_couplingSq`.

The standard held-out evaluator can then consume this generated calibration
without a separate evaluator mode:

```bash
python3 scripts/one_level_benchmark.py \
  /path/to/protocol.json \
  --output-dir /tmp/one-level-evaluation
```

The protocol must bind the generated `calibration.json` by SHA-256 before the
parameter-freeze commit is created.

## Derivation sidecar

`ohmic-rate-derivation.json` records:

- source and generated-calibration digests;
- the exact microscopic inputs;
- derived `gamma`, half-width, full width, and relaxation coefficient;
- the Lean theorem identifier;
- the conditional Born--Markov/secular bridge; and
- `registry_mutation_performed = false`.

The sidecar is not an evidence certificate. A reviewed production benchmark
must retain it alongside the source and generated calibration artifacts.

## Tests

Run:

```bash
python3 scripts/test_derive_one_level_ohmic_rate.py
```

The tests cover:

- exact generation of a standard linewidth calibration;
- deterministic calibration and sidecar digests;
- rejection of a nonpositive cutoff; and
- rejection of an unreviewed formula identifier.

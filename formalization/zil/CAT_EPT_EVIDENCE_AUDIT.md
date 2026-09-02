# CAT/EPT ZIL evidence audit

Base inspected: `entropic-physlib-linear-full@bd17dacbb5118e89eb58acacf11c1da8f9a9cc82`.

## Findings

The formal branch already contains more closure than several earlier status tables report:

- bilinear HLS continuity for Newtonian interaction energy;
- complete-`H¹` Hartree interaction convergence from strong `L^(6/5)` Born-density convergence;
- energy-split no-loss and strong `H¹` convergence;
- normalization closure after strong convergence;
- a Born first-moment direct method;
- compactness of the full minimizing energy level from interaction closure; and
- construction of a nonempty compact uniformly stable minimizing orbit from an explicit conserved flow.

The recurring omission reports were caused by evidence-state drift:

1. standalone `.zc` graphs and embedded Lean declarations had no canonical lifecycle registry;
2. declaration existence and kernel verification were sometimes collapsed into one state;
3. rejected mathematical premises remained listed as open targets;
4. remaining analytic obligations were encoded mainly in prose caveats and could not be queried reliably.

## Rejected omission labels

The following are not valid remaining targets:

- global weak closure of the unit-`L²` sphere;
- unconditional weak lower semicontinuity of attractive translation-invariant energy;
- a bounded `H¹ → H¹` realization of the full spatial Schrödinger generator.

They are replaced by strong no-loss closure, localization-dependent interaction convergence, and a weak `H¹ → H⁻¹` / mild-flow formulation.

## Genuine remaining obligations

- localized strong `L^(6/5)` convergence of recentered Born densities;
- a uniform recentered first-moment bound for the target minimizing family;
- construction of the concrete energy-critical Duhamel/Strichartz flow;
- global continuum mass and energy conservation for that flow; and
- analytic identification of the M9.69 numerical branch with the minimizing orbit.

## Implemented governance

- `Physlib.Meta.ZilEvidenceClosureRegistry` is the Lean-native lifecycle inventory.
- `Physlib.Meta.ZilEvidenceClosureRegistryAudit` links closed records to actual declarations and applies axiom-clean/non-vacuity audits.
- `cat-ept-evidence-closure.zc` exposes implementation, resolution, supersession, dependency, remaining-obligation, and pending-verification queries.

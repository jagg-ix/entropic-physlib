# CAT/EPT evidence-closure queries

Run the graph with the pinned `zil-lean` CLI and inspect these queries:

- `implementation_registry` — claim-to-Lean witness map;
- `resolved_omissions` — rejected omission and counterexample/resolution pairs;
- `superseded_open_labels` — stale labels that should be removed from status tables;
- `remaining_obligations` — only genuinely open analytic targets;
- `dependency_edges` — theorem and obligation dependency graph;
- `awaiting_kernel_checks` — declarations that must not yet be promoted to kernel-checked evidence.

Expected qualitative result:

- seven implemented closure claims;
- three rejected omission labels;
- five remaining analytic obligations;
- all implementation witnesses awaiting the dedicated Lean audit result unless an evidence-only update marks them kernel checked.
